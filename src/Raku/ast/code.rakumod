# A blockoid represents the block part of some kind of code declaration.
class RakuAST::Blockoid is RakuAST::SinkPropagator {
    has RakuAST::StatementList $.statement-list;

    method new(RakuAST::StatementList $statement-list?) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::Blockoid, '$!statement-list',
            $statement-list // RakuAST::StatementList.new);
        $obj
    }

    method propagate-sink(Bool $is-sunk) {
        $!statement-list.propagate-sink($is-sunk, :has-block-parent(True))
    }

    method IMPL-TO-QAST(RakuAST::IMPL::QASTContext $context) {
        $!statement-list.IMPL-TO-QAST($context)
    }

    method visit-children(Code $visitor) {
        $visitor($!statement-list);
    }
}

# Marker for all code-y things.
class RakuAST::Code is RakuAST::Node {
    method IMPL-CLOSURE-QAST(RakuAST::IMPL::QASTContext $context, Bool :$regex) {
        my $code-obj := self.meta-object;
        $context.ensure-sc($code-obj);
        my $clone := QAST::Op.new(
            :op('callmethod'), :name('clone'),
            QAST::WVal.new( :value($code-obj) )
        );
        self.IMPL-TWEAK-REGEX-CLONE($context, $clone) if $regex;
        QAST::Op.new( :op('p6capturelex'), $clone )
    }

    method IMPL-LINK-META-OBJECT(RakuAST::IMPL::QASTContext $context, Mu $block) {
        # Obtain the meta-object and connect it to the code block.
        my $code-obj := self.meta-object;
        $context.ensure-sc($code-obj);
        $block.code_object($code-obj);

        # We need to do a fixup of the code block for the non-precompiled case.
        $context.add-fixup-task(-> {
            QAST::Op.new(
                :op('bindattr'),
                QAST::WVal.new( :value($code-obj) ),
                QAST::WVal.new( :value(Code) ),
                QAST::SVal.new( :value('$!do') ),
                QAST::BVal.new( :value($block) )
            )
        });
    }

    method IMPL-APPEND-SIGNATURE-RETURN(RakuAST::IMPL::QASTContext $context, Mu $qast-stmts) {
        my $signature := self.signature;
        if $signature && $signature.provides-return-value {
            $qast-stmts.push($signature.returns.IMPL-TO-QAST($context));
        }
        $qast-stmts
    }

    method needs-sink-call() { False }

    method signature() { Nil }
}

# A code object that can have placeholder parameters.
class RakuAST::PlaceholderParameterOwner is RakuAST::Node {
    # Any placeholder parameters that have been attached
    has Mu $!attached-placeholder-parameters;

    # A map grouping placeholder parameters by name, for error checking and
    # compilation.
    has Mu $!placeholder-map;

    # Cached generated placeholder signature.
    has RakuAST::Signature $!placeholder-signature;

    method add-placeholder-parameter(RakuAST::VarDeclaration::Placeholder $placeholder) {
        unless nqp::islist($!attached-placeholder-parameters) {
            nqp::bindattr(self, RakuAST::PlaceholderParameterOwner,
                '$!attached-placeholder-parameters', []);
        }
        nqp::push($!attached-placeholder-parameters, $placeholder);
        Nil
    }

    method clear-placeholder-attachments() {
        nqp::bindattr(self, RakuAST::PlaceholderParameterOwner,
            '$!attached-placeholder-parameters', nqp::null());
        Nil
    }

    method has-placeholder-parameters() {
        my $params := $!attached-placeholder-parameters;
        nqp::islist($params) && nqp::elems($params) ?? True !! False
    }

    method IMPL-PLACEHOLDER-MAP() {
        unless nqp::ishash($!placeholder-map) {
            my %map;
            if self.has-placeholder-parameters {
                for $!attached-placeholder-parameters -> $param {
                    my str $key := $param.lexical-name;
                    (%map{$key} || (%map{$key} := [])).push($param);
                }
            }
            nqp::bindattr(self, RakuAST::PlaceholderParameterOwner,
                '$!placeholder-map', %map);
        }
        $!placeholder-map
    }

    # Gets the placeholder signature. Only reliable after resolution has taken
    # place.
    method placeholder-signature() {
        # Return Nil if there isn't one to generate, or the cached one if we have
        # it.
        return Nil unless self.has-placeholder-parameters();
        return $!placeholder-signature if $!placeholder-signature;

        # Group and sort parameters.
        my @positionals;
        my @nameds;
        my @slurpies;
        for self.IMPL-PLACEHOLDER-MAP() {
            my $placeholder := $_.value[0];
            if nqp::istype($placeholder, RakuAST::VarDeclaration::Placeholder::Positional) {
                my int $insert-at := 0;
                my str $desigil-insert := nqp::substr($placeholder.lexical-name, 1);
                while $insert-at < nqp::elems(@positionals) {
                    my str $desigil-cur := nqp::substr(@positionals[$insert-at].lexical-name, 1);
                    last if $desigil-insert lt $desigil-cur;
                    $insert-at++;
                }
                nqp::splice(@positionals, [$placeholder], $insert-at, 0);
            }
            elsif nqp::istype($_, RakuAST::VarDeclaration::Placeholder::Named) {
                @nameds.push($placeholder);
            }
            else {
                @slurpies.push($placeholder);
            }
        }

        # Add to signature.
        my @parameters;
        for @positionals, @nameds, @slurpies -> @placeholders {
            for @placeholders {
                @parameters.push($_.generate-parameter());
            }
        }
        my $signature := RakuAST::Signature.new(:@parameters);
        nqp::bindattr(self, RakuAST::PlaceholderParameterOwner,
            '$!placeholder-signature', $signature);
        $signature
    }
}

# A block, either without signature or with only a placeholder signature.
class RakuAST::Block is RakuAST::LexicalScope is RakuAST::Term is RakuAST::Code is RakuAST::Meta
                     is RakuAST::BlockStatementSensitive is RakuAST::SinkPropagator
                     is RakuAST::Blorst is RakuAST::ImplicitDeclarations
                     is RakuAST::AttachTarget is RakuAST::PlaceholderParameterOwner
                     is RakuAST::BeginTime {
    has RakuAST::Blockoid $.body;

    # Should this block have an implicit topic, in the absence of a (perhaps
    # placeholder) signature?
    # 0 = no implicit topic
    # 1 = optional implicit topic
    # 2 = required implicit topic
    # 3 = required implicit topic populated from exception
    has int $!implicit-topic-mode;

    # Should this block declare a fresh implicit `$/`?
    has int $!fresh-match;

    # Should this block declare a fresh implicit `$!`?
    has int $!fresh-exception;

    method new(RakuAST::Blockoid :$body, Bool :$implicit-topic, Bool :$required-topic) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::Block, '$!body', $body // RakuAST::Blockoid.new);
        nqp::bindattr_i($obj, RakuAST::Block, '$!implicit-topic-mode', 1);
        $obj
    }

    method replace-body(RakuAST::Blockoid $new-body) {
        nqp::bindattr(self, RakuAST::Block, '$!body', $new-body);
        Nil
    }

    method set-implicit-topic(Bool $implicit, Bool :$required, Bool :$exception) {
        nqp::bindattr_i(self, RakuAST::Block, '$!implicit-topic-mode', $implicit
            ?? ($exception ?? 3 !!
                $required  ?? 2 !!
                              1)
            !! 0);
        Nil
    }

    method set-fresh-variables(Bool :$match, Bool :$exception) {
        nqp::bindattr_i(self, RakuAST::Block, '$!fresh-match', $match ?? 1 !! 0);
        nqp::bindattr_i(self, RakuAST::Block, '$!fresh-exception', $exception ?? 1 !! 0);
    }

    method attach-target-names() {
        self.IMPL-WRAP-LIST(['block'])
    }

    method clear-attachments() {
        self.clear-handler-attachments();
        self.clear-placeholder-attachments();
        Nil
    }

    method propagate-sink(Bool $is-sunk) {
        $!body.apply-sink($is-sunk);
    }

    method PRODUCE-IMPLICIT-DECLARATIONS() {
        my @implicit;
        unless self.signature || self.placeholder-signature {
            if $!implicit-topic-mode == 1 {
                @implicit[0] := RakuAST::VarDeclaration::Implicit::TopicParameter.new;
            }
            elsif $!implicit-topic-mode == 2 {
                @implicit[0] := RakuAST::VarDeclaration::Implicit::TopicParameter.new(:required);
            }
            elsif $!implicit-topic-mode == 3 {
                @implicit[0] := RakuAST::VarDeclaration::Implicit::TopicParameter.new(:required,
                    :exception);
            }
        }
        if $!fresh-match {
            nqp::push(@implicit, RakuAST::VarDeclaration::Implicit::Special.new(:name('$/')));
        }
        if $!fresh-exception {
            nqp::push(@implicit, RakuAST::VarDeclaration::Implicit::Special.new(:name('$!')));
        }
        self.IMPL-WRAP-LIST(@implicit)
    }

    method is-begin-performed-before-children() { False }

    method PERFORM-BEGIN(RakuAST::Resolver $resolver) {
        # Make sure that our placeholder signature has resolutions performed.
        my $placeholder-signature := self.placeholder-signature;
        if $placeholder-signature {
            $placeholder-signature.IMPL-CHECK($resolver, True);
        }
        Nil
    }

    method PRODUCE-META-OBJECT() {
        # Create block object and install signature. If it doesn't have one, then
        # we can create it based upon the implicit topic it may or may not have.
        my $block := nqp::create(Block);
        my $signature := self.signature || self.placeholder-signature;
        if $signature {
            nqp::bindattr($block, Code, '$!signature', $signature.meta-object);
        }
        elsif $!implicit-topic-mode {
            my constant REQUIRED-TOPIC-SIG := -> {
                my $param := nqp::create(Parameter);
                nqp::bindattr_s($param, Parameter, '$!variable_name', '$_');
                my $sig := nqp::create(Signature);
                nqp::bindattr($sig, Signature, '@!params', [$param]);
                nqp::bindattr_i($sig, Signature, '$!arity', 1);
                nqp::bindattr($sig, Signature, '$!count', nqp::box_i(1, Int));
                $sig
            }();
            my constant OPTIONAL-TOPIC-SIG := -> {
                my $param := nqp::create(Parameter);
                nqp::bindattr_s($param, Parameter, '$!variable_name', '$_');
                nqp::bindattr_i($param, Parameter, '$!flags', 2048 + 16384); # Optional + default from outer
                my $sig := nqp::create(Signature);
                nqp::bindattr($sig, Signature, '@!params', [$param]);
                nqp::bindattr_i($sig, Signature, '$!arity', 0);
                nqp::bindattr($sig, Signature, '$!count', nqp::box_i(1, Int));
                $sig
            }();
            nqp::bindattr($block, Code, '$!signature', $!implicit-topic-mode == 1
                ?? OPTIONAL-TOPIC-SIG
                !! REQUIRED-TOPIC-SIG);
        }
        $block
    }

    method IMPL-QAST-FORM-BLOCK(RakuAST::IMPL::QASTContext $context, str $blocktype) {
        # Form block with declarations.
        my $block := QAST::Block.new(
            :$blocktype,
            self.IMPL-QAST-DECLS($context)
        );

        # Compile body and, if needed, a signature, and set up arity and any
        # exception rethrow logic.
        my $body-qast := self.IMPL-APPEND-SIGNATURE-RETURN($context,
            $!body.IMPL-TO-QAST($context));
        my $signature := self.signature || self.placeholder-signature;
        if $signature {
            $block.push($signature.IMPL-TO-QAST($context));
            $block.arity($signature.arity);
            $block.annotate('count', $signature.count);
        }
        elsif $!implicit-topic-mode == 1 {
            $block.arity(0);
            $block.annotate('count', 1);
        }
        elsif $!implicit-topic-mode >= 2 {
            $block.arity(1);
            $block.annotate('count', 1);
        }

        my $is-handler := $!implicit-topic-mode == 3 ?? True !! False;
        $block.push(self.IMPL-WRAP-SCOPE-HANDLER-QAST($context, $body-qast, :$is-handler));
        $block
    }

    method IMPL-QAST-DECL-CODE(RakuAST::IMPL::QASTContext $context) {
        # Form the block itself and link it with the meta-object.
        my $block := self.IMPL-QAST-FORM-BLOCK($context, 'declaration_static');
        self.IMPL-LINK-META-OBJECT($context, $block);
        $block
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context, :$immediate) {
        if $immediate {
            # For now, assume we never need a code object for such a block. The
            # closure clone is done for us by the QAST compiler.
            self.IMPL-QAST-FORM-BLOCK($context, 'immediate')
        }
        else {
            # Not immediate, so already produced as a declaration above; just
            # closure clone it. Only invoke if it's a bare block.
            my $ast := self.IMPL-CLOSURE-QAST($context);
            self.bare-block
                ?? QAST::Op.new( :op('call'), $ast )
                !! $ast
        }
    }

    method bare-block() {
        self.is-block-statement
    }

    # Applies the block or hash disambiguation algorithm, to determine whether
    # a circumfix:<{ }> should compile as a block or a hash. If it should
    # compile as a block, returns identity. Otherwise, returns an instance of
    # RakuAST::Circumfix::HashComposer. Note that this method - nor the block
    # vs hash distinction - does NOT impact upon the compilation of this node
    # if it is in the AST. This method is for use by a compiler that may have
    # parsed things tentatively as a block to obtain the actual node to use.
    # If constructing AST synthetically, just make the correct thing in the
    # first place.
    method block-or-hash() {
        my @statements := self.IMPL-UNWRAP-LIST(self.body.statement-list.statements);
        my int $num-statements := nqp::elems(@statements);
        if $num-statements == 0 {
            # Empty block is always an empty hash composer
            RakuAST::Circumfix::HashComposer.new
        }
        elsif $num-statements > 1 {
            # Multiple statements is always a block
            self
        }
        else {
            # Must be an expression statement.
            my $statement := @statements[0];
            unless nqp::istype($statement, RakuAST::Statement::Expression) {
                return self;
            }
            my $expression := $statement.expression;

            # If it's a comma list, then obtain the first element. Otherwise,
            # we have the thing to test already.
            my int $is-comma := nqp::istype($expression, RakuAST::ApplyListInfix) &&
                nqp::istype($expression.infix, RakuAST::Infix) &&
                $expression.infix.operator eq ',';
            my $test := $is-comma
                ?? self.IMPL-UNWRAP-LIST($expression.operands)[0]
                !! $expression;

            # It's a block unless we have:
            return self unless
                # A fatarrow or colonpair
                nqp::istype($test, RakuAST::FatArrow) ||
                nqp::istype($test, RakuAST::ColonPair) ||
                # The Pair infix operator
                nqp::istype($test, RakuAST::ApplyInfix) &&
                    nqp::istype($test.infix, RakuAST::Infix) &&
                    $test.infix.operator eq '=>' ||
                # A hash sigil'd variable
                nqp::istype($test, RakuAST::Var) && $test.sigil eq '%';

            # Looks like a hash, but check for declarations or $_ usage.
            my int $seen-decl-or-topic;
            $expression.visit: -> $node {
                # Don't walk into other scopes
                if nqp::istype($node, RakuAST::LexicalScope) {
                    0
                }
                # If it's a declaration, it blocks; walk no futher
                elsif nqp::istype($node, RakuAST::Declaration) {
                    $seen-decl-or-topic := 1;
                    0
                }
                # If it's a usage of the topic, it also blocks; walk no further
                elsif nqp::istype($node, RakuAST::Var::Lexical) && $node.name eq '$_' ||
                    nqp::istype($node, RakuAST::Term::TopicCall) {
                    $seen-decl-or-topic := 1;
                    0
                }
                # Otherwise, keep looking
                else {
                    1
                }
            }
            $seen-decl-or-topic
                ?? self
                !! RakuAST::Circumfix::HashComposer.new($expression)
        }
    }

    method visit-children(Code $visitor) {
        $visitor($!body);
    }
}

# A pointy block (-> $foo { ... }).
class RakuAST::PointyBlock is RakuAST::Block {
    has RakuAST::Signature $.signature;

    method new(RakuAST::Signature :$signature, RakuAST::Blockoid :$body) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::PointyBlock, '$!signature', $signature
            // RakuAST::Signature.new);
        nqp::bindattr($obj, RakuAST::Block, '$!body', $body // RakuAST::Blockoid.new);
        $obj
    }

    method replace-signature(RakuAST::Signature $new-signature) {
        nqp::bindattr(self, RakuAST::PointyBlock, '$!signature', $new-signature);
        Nil
    }

    method bare-block() { False }

    method propagate-sink(Bool $is-sunk) {
        self.body.apply-sink($is-sunk);
        $!signature.apply-sink(True);
    }

    method visit-children(Code $visitor) {
        $visitor($!signature);
        $visitor(self.body);
    }
}

# Done by all kinds of Routine.
class RakuAST::Routine is RakuAST::LexicalScope is RakuAST::Term is RakuAST::Code
                       is RakuAST::Meta is RakuAST::Declaration
                       is RakuAST::ImplicitDeclarations is RakuAST::AttachTarget
                       is RakuAST::PlaceholderParameterOwner
                       is RakuAST::BeginTime is RakuAST::TraitTarget {
    has RakuAST::Name $.name;
    has RakuAST::Signature $.signature;

    method replace-name(RakuAST::Name $new-name) {
        nqp::bindattr(self, RakuAST::Routine, '$!name', $new-name);
        Nil
    }

    method replace-signature(RakuAST::Signature $new-signature) {
        nqp::bindattr(self, RakuAST::Routine, '$!signature', $new-signature);
        Nil
    }

    method attach-target-names() {
        self.IMPL-WRAP-LIST(['routine', 'block'])
    }

    method clear-attachments() {
        self.clear-handler-attachments();
        self.clear-placeholder-attachments();
        Nil
    }

    method PRODUCE-META-OBJECT() {
        my $routine := nqp::create(self.IMPL-META-OBJECT-TYPE);
        my $signature := self.placeholder-signature || self.signature;
        nqp::bindattr($routine, Code, '$!signature', $signature.meta-object);
        $routine
    }

    method is-begin-performed-before-children() { False }

    method PERFORM-BEGIN(RakuAST::Resolver $resolver) {
        # Make sure that our placeholder signature has resolutions performed.
        my $placeholder-signature := self.placeholder-signature;
        if $placeholder-signature {
            $placeholder-signature.IMPL-CHECK($resolver, True);
        }
        # Apply any traits.
        self.apply-traits($resolver, self)
    }

    method PRODUCE-IMPLICIT-DECLARATIONS() {
        self.IMPL-WRAP-LIST([
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$/')),
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$!')),
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$_')),
        ])
    }

    method IMPL-QAST-FORM-BLOCK(RakuAST::IMPL::QASTContext $context) {
        my $block := QAST::Block.new(
            :blocktype('declaration_static'),
            self.IMPL-QAST-DECLS($context)
        );
        my $signature := self.placeholder-signature || $!signature;
        $block.push($signature.IMPL-TO-QAST($context));
        $block.arity($signature.arity);
        $block.annotate('count', $signature.count);
        $block.push(self.IMPL-COMPILE-BODY($context));
        $block
    }

    method IMPL-COMPILE-BODY(RakuAST::IMPL::QASTContext $context) {
        nqp::die('RakuAST::Routine subclass must implement IMPL-COMPILE-BODY')
    }

    method IMPL-WRAP-RETURN-HANDLER(RakuAST::IMPL::QASTContext $context, RakuAST::Node $body) {
        my $result := $body;
        my $routine := self.compile-time-value;
        my $signature := nqp::getattr($routine, Code, '$!signature');
        $context.ensure-sc($routine);

        # Add return exception and decont handler if needed.
        # TODO optimize out if provably no return call
        my str $decont-rv-op := $context.lang-version lt 'd' && $context.is-moar
            ?? 'p6decontrv_6c'
            !! 'p6decontrv';
        $result := QAST::Op.new(
            :op<handlepayload>,
            QAST::Op.new( :op($decont-rv-op), QAST::WVal.new( :value($routine) ), $result ),
            'RETURN',
            QAST::Op.new( :op<lastexpayload> )
        );

        # Add return type check if needed.
        # TODO also infer body type
        my $returns := nqp::ifnull($signature.returns, Mu);
        unless $returns =:= Mu || $returns =:= Nil || nqp::isconcrete($returns) {
            $result := QAST::Op.new(
                :op('p6typecheckrv'),
                $result,
                QAST::WVal.new( :value($routine) ),
                QAST::WVal.new( :value(Nil) )
            );
        }

        $result
    }

    method IMPL-QAST-DECL-CODE(RakuAST::IMPL::QASTContext $context) {
        # Form the QAST block itself and link it with the meta-object.
        my $block := self.IMPL-QAST-FORM-BLOCK($context);
        self.IMPL-LINK-META-OBJECT($context, $block);

        # Set a name, if there is one.
        if $!name {
            my $canon-name := $!name.canonicalize;
            $block.name($canon-name);
        }

        $block
    }

    method IMPL-QAST-DECL(RakuAST::IMPL::QASTContext $context) {
        # If we're a named lexical thing, install us in the block.
        my $name := self.lexical-name;
        if $name && self.scope eq 'my' {
            QAST::Op.new(
                :op('bind'),
                QAST::Var.new( :decl<var>, :scope<lexical>, :$name ),
                self.IMPL-CLOSURE-QAST($context)
            )
        }
        else {
            QAST::Op.new( :op('null') )
        }
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        if self.scope eq 'my' {
            my $canon-name := $!name.canonicalize;
            QAST::Var.new( :scope<lexical>, :name('&' ~ $canon-name) )
        }
        else {
            self.IMPL-CLOSURE-QAST($context)
        }
    }

    method lexical-name() {
        my $name := self.name;
        if $name {
            '&' ~ $name.canonicalize
        }
        else {
            Nil
        }
    }

    method generate-lookup() {
        if self.is-lexical {
            my $lookup := RakuAST::Var::Lexical.new(self.lexical-name);
            $lookup.set-resolution(self);
            $lookup
        }
        else {
            nqp::die('Cannot generate lookup of a routine for scope ' ~ self.scope);
        }
    }

    method IMPL-LOOKUP-QAST(RakuAST::IMPL::QASTContext $context, Mu :$rvalue) {
        QAST::Var.new( :scope('lexical'), :name(self.lexical-name) )
    }

    method visit-children(Code $visitor) {
        $visitor($!name) if $!name;
        $visitor($!signature);
        self.visit-traits($visitor);
        $visitor(self.body);
    }
}

# A subroutine.
class RakuAST::Sub is RakuAST::Routine is RakuAST::SinkBoundary {
    has RakuAST::Blockoid $.body;

    method new(str :$scope, RakuAST::Name :$name, RakuAST::Signature :$signature,
            List :$traits, RakuAST::Blockoid :$body) {
        my $obj := nqp::create(self);
        nqp::bindattr_s($obj, RakuAST::Declaration, '$!scope', $scope);
        nqp::bindattr($obj, RakuAST::Routine, '$!name', $name // RakuAST::Name);
        nqp::bindattr($obj, RakuAST::Routine, '$!signature', $signature
            // RakuAST::Signature.new);
        nqp::bindattr($obj, RakuAST::Sub, '$!body', $body // RakuAST::Blockoid.new);
        $obj.set-traits($traits);
        $obj
    }

    method replace-body(RakuAST::Blockoid $new-body) {
        nqp::bindattr(self, RakuAST::Sub, '$!body', $new-body);
        Nil
    }

    method IMPL-META-OBJECT-TYPE() { Sub }

    method default-scope() {
        self.name ?? 'my' !! 'anon'
    }

    method allowed-scopes() {
        self.IMPL-WRAP-LIST(['my', 'anon', 'our'])
    }

    method get-boundary-sink-propagator() {
        $!body.statement-list
    }

    method is-boundary-sunk() {
        my $signature := self.signature;
        $signature ?? $signature.provides-return-value !! False
    }

    method IMPL-COMPILE-BODY(RakuAST::IMPL::QASTContext $context) {
        self.IMPL-WRAP-RETURN-HANDLER($context,
            self.IMPL-WRAP-SCOPE-HANDLER-QAST($context,
                self.IMPL-APPEND-SIGNATURE-RETURN($context, $!body.IMPL-TO-QAST($context))))
    }
}

# The commonalities of method-like things, whichever language their body is in
# (be it the main Raku language or the regex language).
class RakuAST::Methodish is RakuAST::Routine is RakuAST::Attaching {
    method default-scope() {
        self.name ?? 'has' !! 'anon'
    }

    method allowed-scopes() {
        self.IMPL-WRAP-LIST(['has', 'my', 'anon', 'our'])
    }

    method attach(RakuAST::Resolver $resolver) {
        if self.scope eq 'has' {
            my $package := $resolver.find-attach-target('package');
            if $package {
                $package.ATTACH-METHOD(self);
            }
            else {
                # TODO check-time problem
            }
        }
    }
}

# A method.
class RakuAST::Method is RakuAST::Methodish is RakuAST::SinkBoundary {
    has RakuAST::Blockoid $.body;

    method new(str :$scope, RakuAST::Name :$name, RakuAST::Signature :$signature,
            List :$traits, RakuAST::Blockoid :$body) {
        my $obj := nqp::create(self);
        nqp::bindattr_s($obj, RakuAST::Declaration, '$!scope', $scope);
        nqp::bindattr($obj, RakuAST::Routine, '$!name', $name // RakuAST::Name);
        nqp::bindattr($obj, RakuAST::Routine, '$!signature', $signature
            // RakuAST::Signature.new);
        nqp::bindattr($obj, RakuAST::Method, '$!body', $body // RakuAST::Blockoid.new);
        $obj.set-traits($traits);
        $obj
    }

    method replace-body(RakuAST::Blockoid $new-body) {
        nqp::bindattr(self, RakuAST::Method, '$!body', $new-body);
        Nil
    }

    method IMPL-META-OBJECT-TYPE() { Method }

    method PRODUCE-IMPLICIT-DECLARATIONS() {
        self.IMPL-WRAP-LIST([
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$/')),
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$!')),
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$_')),
            RakuAST::VarDeclaration::Implicit::Self.new(),
        ])
    }

    method get-boundary-sink-propagator() {
        $!body.statement-list
    }

    method is-boundary-sunk() {
        my $signature := self.signature;
        $signature ?? $signature.provides-return-value !! False
    }

    method IMPL-COMPILE-BODY(RakuAST::IMPL::QASTContext $context) {
        self.IMPL-WRAP-RETURN-HANDLER($context,
            self.IMPL-WRAP-SCOPE-HANDLER-QAST($context,
                self.IMPL-APPEND-SIGNATURE-RETURN($context, $!body.IMPL-TO-QAST($context))))
    }
}

# A submethod.
class RakuAST::Submethod is RakuAST::Method {
    method IMPL-META-OBJECT-TYPE() { Submethod }
}

# A regex declaration, such as `token foo { bar }`. This implies its own
# lexical scope.
class RakuAST::RegexDeclaration is RakuAST::Methodish {
    has RakuAST::Regex $.body;

    method new(str :$scope, RakuAST::Name :$name, RakuAST::Signature :$signature,
            List :$traits, RakuAST::Regex :$body) {
        my $obj := nqp::create(self);
        nqp::bindattr_s($obj, RakuAST::Declaration, '$!scope', $scope);
        nqp::bindattr($obj, RakuAST::Routine, '$!name', $name // RakuAST::Name);
        nqp::bindattr($obj, RakuAST::Routine, '$!signature',
            $signature // RakuAST::Signature.new);
        nqp::bindattr($obj, RakuAST::RegexDeclaration, '$!body',
            $body // RakuAST::Regex::Assertion::Fail.new);
        $obj.set-traits($traits);
        $obj
    }

    method replace-body(RakuAST::Regex $new-body) {
        nqp::bindattr(self, RakuAST::RegexDeclaration, '$!body', $new-body);
        Nil
    }

    method IMPL-META-OBJECT-TYPE() { Regex }

    method PRODUCE-IMPLICIT-DECLARATIONS() {
        self.IMPL-WRAP-LIST([
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$/')),
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$!')),
            RakuAST::VarDeclaration::Implicit::Special.new(:name('$_')),
            RakuAST::VarDeclaration::Implicit::Self.new(),
            RakuAST::VarDeclaration::Implicit::Cursor.new(),
        ])
    }

    method IMPL-COMPILE-BODY(RakuAST::IMPL::QASTContext $context) {
        QAST::Stmts.new(
            # Regex compiler wants a local named "self"
            QAST::Op.new(
                :op('bind'),
                QAST::Var.new( :decl('var'), :scope('local'), :name('self') ),
                QAST::Var.new( :scope('lexical'), :name('self') )
            ),
            $!body.IMPL-REGEX-TOP-LEVEL-QAST($context, self.meta-object, nqp::hash())
        )
    }
}

# Done by things that "thunk" a regex - that is to say, they want to compile as
# a separate regex code object but without introducing a new lexical scope. This
# includes quoted regexes like /.../, capturing groups, and calls of the form
# `<?before foo>`, where `foo` is the thunked regex.
class RakuAST::RegexThunk is RakuAST::Code is RakuAST::Meta {
    method PRODUCE-META-OBJECT() {
        # Create default signature, receiving invocant only.
        my $signature := nqp::create(Signature);
        my $parameter := nqp::create(Parameter);
        nqp::bindattr($parameter, Parameter, '$!type', Mu);
        nqp::bindattr($signature, Signature, '@!params', nqp::list($parameter));

        # Create Regex object.
        my $regex := nqp::create(Regex);
        nqp::bindattr($regex, Code, '$!signature', $signature);
        $regex
    }

    method IMPL-QAST-FORM-BLOCK(RakuAST::IMPL::QASTContext $context, str $blocktype) {
        my $slash := RakuAST::VarDeclaration::Implicit::Special.new(:name('$/'));
        QAST::Block.new(
            :blocktype('declaration_static'),
            QAST::Var.new( :decl('var'), :scope('local'), :name('self') ),
            QAST::Var.new( :decl('var'), :scope('lexical'), :name('$¢') ),
            $slash.IMPL-QAST-DECL($context),
            QAST::Var.new(
                :decl('param'), :scope('local'), :name('__lowered_param'),
                QAST::Op.new(
                    :op('bind'),
                    QAST::Var.new( :scope('local'), :name('self') ),
                    QAST::Op.new(
                        :op('decont'),
                        QAST::Var.new( :scope('local'), :name('__lowered_param') )
                    )
                )
            ),
            self.IMPL-THUNKED-REGEX-QAST($context)
        )
    }
}

# A quoted regex, such as `/abc/` or `rx/def/` or `m/ghi/`. Does not imply a
# new lexical scope.
class RakuAST::QuotedRegex is RakuAST::RegexThunk is RakuAST::Term
                           is RakuAST::Sinkable is RakuAST::ImplicitLookups
                           is RakuAST::CheckTime {
    has RakuAST::Regex $.body;
    has Bool $.match-immediately;
    has List $.adverbs;

    method new(RakuAST::Regex :$body, Bool :$match-immediately, List :$adverbs) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::QuotedRegex, '$!body',
            $body // RakuAST::Regex::Assertion::Fail.new);
        nqp::bindattr($obj, RakuAST::QuotedRegex, '$!match-immediately',
            $match-immediately ?? True !! False);
        $obj.replace-adverbs($adverbs // []);
        $obj
    }

    method replace-body(RakuAST::Regex $new-body) {
        nqp::bindattr(self, RakuAST::QuotedRegex, '$!body', $new-body);
        Nil
    }

    method replace-adverbs(List $adverbs) {
        my @checked-adverbs;
        if $adverbs {
            for self.IMPL-UNWRAP-LIST($adverbs) {
                unless nqp::istype($_, RakuAST::QuotePair) {
                    nqp::die('A regex adverb may only be a RakuAST::QuotePair');
                }
                nqp::push(@checked-adverbs, $_);
            }
        }
        nqp::bindattr(self, RakuAST::QuotedRegex, '$!adverbs', @checked-adverbs);
        Nil
    }

    method PRODUCE-IMPLICIT-LOOKUPS() {
        self.IMPL-WRAP-LIST([
            RakuAST::Var::Lexical.new('$_'),
            RakuAST::Var::Lexical.new('$/'),
            RakuAST::Type::Setting.new(RakuAST::Name.from-identifier-parts(
                'Rakudo', 'Internals', 'RegexBoolification6cMarker'
            ))
        ])
    }

    method IMPL-NORMALIZE-ADVERB(str $adverb) {
        my constant NORMS := nqp::hash(
            'ignorecase',   'i',
            'ignoremark',   'm',
            'ratchet',      'r',
            'sigspace',     's',
            'continue',     'c',
            'pos',          'p',
            'th',           'nth',
            'st',           'nth',
            'nd',           'nth',
            'rd',           'nth',
            'global',       'g',
            'overlap',      'ov',
            'exhaustive',   'ex',
            'Perl5',        'P5',
            'samecase',     'ii',
            'samespace',    'ss',
            'samemark',     'mm',
            'squash',       's',
            'complement',   'c',
            'delete',       'd'
        );
        NORMS{$adverb} // $adverb
    }

    method IMPL-IS-COMPILATION-ADVERB(str $norm-adverb) {
        my constant COMPS := nqp::hash('i', 1, 'm', 1, 'r', 1, 's', 1, 'P5', 1);
        nqp::existskey(COMPS, $norm-adverb)
    }

    method IMPL-IS-POSITION-ADVERB(str $norm-adverb) {
        my constant POS := nqp::hash('c', 1, 'p', 1);
        nqp::existskey(POS, $norm-adverb)
    }

    method IMPL-IS-MULTIPLE-ADVERB(str $norm-adverb) {
        my constant POS := nqp::hash('x', 1, 'g', 1, 'ov', 1, 'ex', 1);
        nqp::existskey(POS, $norm-adverb)
    }

    method IMPL-IS-IMMEDIATE-MATCH-ADVERB(str $norm-adverb) {
        $norm-adverb eq 'nth' || self.IMPL-IS-POSITION-ADVERB($norm-adverb) ||
            self.IMPL-IS-MULTIPLE-ADVERB($norm-adverb)
    }

    method PERFORM-CHECK(RakuAST::Resolver $resolver) {
        # Check adverbs
        for self.IMPL-UNWRAP-LIST($!adverbs) {
            my str $key := $_.key;
            my str $norm := self.IMPL-NORMALIZE-ADVERB($key);
            if self.IMPL-IS-COMPILATION-ADVERB($norm) {
                # Compile-time adverbs must have a simple compile time value.
                unless nqp::isconcrete($_.simple-compile-time-quote-value()) {
                    self.add-sorry: $resolver.build-exception:
                        'X::Value::Dynamic', what => "Adverb $key";
                }
            }
            elsif !($!match-immediately && self.IMPL-IS-IMMEDIATE-MATCH-ADVERB($norm)) {
                # Not applicable to the construct, so report.
                self.add-sorry: $resolver.build-exception:
                    'X::Syntax::Regex::Adverb',
                    adverb    => $key,
                    construct => $!match-immediately ?? 'm' !! 'rx'
            }
        }
    }

    method IMPL-THUNKED-REGEX-QAST(RakuAST::IMPL::QASTContext $context) {
        # Obtain adverbs that affect compilation and install them into
        # the %mods hash.
        my %mods;
        for self.IMPL-UNWRAP-LIST($!adverbs) {
            my str $norm := self.IMPL-NORMALIZE-ADVERB($_.key);
            if self.IMPL-IS-COMPILATION-ADVERB($norm) {
                %mods{$norm} := $_.simple-compile-time-quote-value() ?? 1 !! 0;
            }
        }
        $!body.IMPL-REGEX-TOP-LEVEL-QAST($context, self.meta-object, %mods)
    }

    method IMPL-QAST-DECL-CODE(RakuAST::IMPL::QASTContext $context) {
        # Form the block itself and link it with the meta-object.
        my $block := self.IMPL-QAST-FORM-BLOCK($context, 'declaration_static');
        self.IMPL-LINK-META-OBJECT($context, $block);
        $block
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my $closure := self.IMPL-CLOSURE-QAST($context, :regex);
        if $!match-immediately {
            my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups);
            my $topic := @lookups[0].IMPL-TO-QAST($context);
            my $match-qast := QAST::Op.new(
                :op('callmethod'), :name('match'),
                $topic, $closure );
            my int $is-multiple-match := 0;
            for self.IMPL-UNWRAP-LIST($!adverbs) {
                my str $norm := self.IMPL-NORMALIZE-ADVERB($_.key);
                if self.IMPL-IS-POSITION-ADVERB($norm) {
                    # These need to be passed the end of the last match.
                    my $slash := @lookups[1].IMPL-TO-QAST($context);
                    $match-qast.push: QAST::Op.new:
                        :named($norm), :op<if>,
                        $slash,
                        QAST::Op.new( :op<callmethod>, :name<to>, $slash ),
                        QAST::IVal.new( :value(0) )
                }
                else {
                    # Pass the value of the pair.
                    my $arg := $_.value.IMPL-TO-QAST($context);
                    $arg.named($_.key);
                    $match-qast.push($arg);
                    $is-multiple-match := 1 if self.IMPL-IS-MULTIPLE-ADVERB($norm);
                }
            }
            if $is-multiple-match {
                # Don't update $/ in the list case
                $match-qast
            }
            else {
                my $slash := @lookups[1].IMPL-TO-QAST($context);
                QAST::Op.new( :op('p6store'), $slash, $match-qast )
            }
        }
        else {
            self.sunk
                ?? QAST::Op.new( :op('callmethod'), :name('Bool'), $closure )
                !! $closure
        }
    }

    method IMPL-TWEAK-REGEX-CLONE(RakuAST::IMPL::QASTContext $context, Mu $clone) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups);
        if $context.lang-version lt 'd' {
            my $topic := @lookups[2].IMPL-TO-QAST($context);
            $topic.named('topic');
            $clone.push($topic);
        }
        else {
            my $topic := @lookups[0].IMPL-TO-QAST($context);
            $topic.named('topic');
            $clone.push($topic);
            my $slash := @lookups[1].IMPL-TO-QAST($context);
            $slash.named('slash');
            $clone.push($slash);
        }
        Nil
    }

    method visit-children(Code $visitor) {
        for self.IMPL-UNWRAP-LIST($!adverbs) {
            $visitor($_);
        }
        $visitor($!body);
    }
}
