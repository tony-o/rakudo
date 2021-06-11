class RakuAST::IntLiteral is RakuAST::Term is RakuAST::CompileTimeValue {
    has Int $.value;
    
    method new(Int $value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::IntLiteral, '$!value', $value);
        $obj
    }

    method type {
        $!value.WHAT
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := $!value;
        $context.ensure-sc($value);
        my $wval := QAST::WVal.new( :$value );
        nqp::isbig_I($value)
            ?? $wval
            !! QAST::Want.new( $wval, 'Ii', QAST::IVal.new( :value(nqp::unbox_i($value)) ) )
    }

    method compile-time-value() { $!value }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) { $!value }
}

class RakuAST::NumLiteral is RakuAST::Term is RakuAST::CompileTimeValue {
    has Num $.value;

    method new(Num $value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::NumLiteral, '$!value', $value);
        $obj
    }

    method type {
        $!value.WHAT
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := $!value;
        $context.ensure-sc($value);
        my $wval := QAST::WVal.new( :$value );
        QAST::Want.new( $wval, 'Nn', QAST::NVal.new( :value(nqp::unbox_n($value)) ) )
    }

    method compile-time-value() { $!value }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) { $!value }
}

class RakuAST::RatLiteral is RakuAST::Term is RakuAST::CompileTimeValue {
    has Rat $.value;

    method new(Rat $value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::RatLiteral, '$!value', $value);
        $obj
    }

    method type {
        $!value.WHAT
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := $!value;
        $context.ensure-sc($value);
        QAST::WVal.new( :$value )
    }

    method compile-time-value() { $!value }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) { $!value }
}

class RakuAST::VersionLiteral is RakuAST::Term is RakuAST::CompileTimeValue {
    has Any $.value;

    method new($value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::VersionLiteral, '$!value', $value);
        $obj
    }

    method type {
        $!value.WHAT
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := $!value;
        $context.ensure-sc($value);
        QAST::WVal.new( :$value )
    }

    method compile-time-value() { $!value }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) { $!value }
}

# A StrLiteral is a basic string literal without any kind of interpolation
# taking place. It may be placed in the tree directly, but a compiler will
# typically emit it in a quoted string wrapper.
class RakuAST::StrLiteral is RakuAST::Term is RakuAST::CompileTimeValue {
    has Str $.value;

    method new(Str $value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::StrLiteral, '$!value', $value);
        $obj
    }

    method type {
        $!value.WHAT
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := $!value;
        $context.ensure-sc($value);
        my $wval := QAST::WVal.new( :$value );
        QAST::Want.new( $wval, 'Ss', QAST::SVal.new( :value(nqp::unbox_s($value)) ) )
    }

    method compile-time-value() { $!value }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) { $!value }
}

# A quoted string consists of a sequence of segments that should be evaluated
# (if needed) and concatenated. Processing may be applied to the result (these
# are "words", "quotewords", "val", and "exec", and are applied in the order
# that they are specified here).
class RakuAST::QuotedString is RakuAST::Term is RakuAST::ImplicitLookups {
    has Mu $!segments;
    has Mu $!processors;

    method new(List :$segments!, List :$processors) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::QuotedString, '$!segments',
            self.IMPL-UNWRAP-LIST($segments));
        nqp::bindattr($obj, RakuAST::QuotedString, '$!processors',
            self.IMPL-CHECK-PROCESSORS($processors));
        $obj
    }

    method IMPL-CHECK-PROCESSORS(Mu $processors) {
        my constant VALID := nqp::hash('words', Mu, 'quotewords', Mu, 'val', Mu, 'exec', 'Mu');
        my @result;
        for self.IMPL-UNWRAP-LIST($processors // []) {
            if nqp::existskey(VALID, $_) {
                nqp::push(@result, nqp::box_s($_, Str));
            }
            else {
                nqp::die("Unsupported quoted string processor '$_'");
            }
        }
        @result
    }

    method segments() {
        self.IMPL-WRAP-LIST($!segments)
    }

    method processors() {
        self.IMPL-WRAP-LIST($!processors)
    }

    method PRODUCE-IMPLICIT-LOOKUPS() {
        my @needed;
        if nqp::elems($!processors) {
            for $!processors {
                if $_ eq 'val' {
                    nqp::push(@needed, RakuAST::Var::Lexical::Setting.new('&val'));
                    last;
                }
            }
        }
        self.IMPL-WRAP-LIST(@needed)
    }

    method type {
        if $!processors {
            # Can probably figure some of these out.
            Mu
        }
        else {
            # Always a string if no processors.
            Str
        }
    }

    # Tries to get a literal value for the quoted string. If that is not
    # possible, returns Nil.
    method literal-value() {
        my $base-str;
        if nqp::elems($!segments) == 1 && nqp::istype($!segments[0], RakuAST::StrLiteral) {
            $base-str := $!segments[0].value;
        }
        else {
            my str $base-from-parts := '';
            for $!segments {
                if nqp::istype($_, RakuAST::StrLiteral) {
                    $base-from-parts := $base-from-parts ~ $_.value;
                }
                else {
                    return Nil;
                }
            }
            $base-str := nqp::box_s($base-from-parts, Str);
        }
        my $result := $base-str;
        for $!processors {
            if $_ eq 'words' {
                return Nil unless nqp::istype($result, Str);
                $result := $result.WORDS_AUTODEREF();
            }
            elsif $_ eq 'val' {
                my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups);
                my $val := @lookups[0].resolution.compile-time-value;
                $result := $val($result);
            }
            else {
                return Nil;
            }
        }
        return $result;
    }

    # Checks if this is an empty words list, as seen in a form like %h<>.
    method is-empty-words() {
        # Is it empty?
        return False if nqp::elems($!segments) >= 2;
        if nqp::elems($!segments) == 1 {
            my $seg := $!segments[0];
            return False unless nqp::istype($seg, RakuAST::StrLiteral) && $seg.value eq '';
        }

        # Yes, but is it quote words?
        for $!processors {
            if $_ eq 'words' {
                return True;
            }
        }
        False
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        # If we can constant fold it, just produce the constant.
        my $literal-value := self.literal-value;
        if nqp::isconcrete($literal-value) {
            $context.ensure-sc($literal-value);
            return QAST::WVal.new( :value($literal-value) );
        }

        # Otherwise, needs compilation.
        my @segment-asts;
        for $!segments {
            if $_.type =:= Str {
                @segment-asts.push($_.IMPL-TO-QAST($context));
            }
            else {
                my $inter-qast := $_.IMPL-TO-QAST($context);
                if nqp::istype($_, RakuAST::Block) {
                    $inter-qast := QAST::Op.new( :op('call'), $inter-qast );
                }
                @segment-asts.push(QAST::Op.new(
                    :op('callmethod'), :name('Str'),
                    $inter-qast
                ));
            }
        }
        my int $seg-count := nqp::elems(@segment-asts);
        my $qast;
        if $seg-count == 1 {
            $qast := @segment-asts[0];
        }
        elsif $seg-count == 2 {
            $qast := QAST::Op.new( :op('concat'), @segment-asts[0], @segment-asts[1] )
        }
        else {
            $qast := QAST::Op.new(
                :op('join'),
                QAST::SVal.new( :value('') ),
                QAST::Op.new( :op('list_s'), |@segment-asts )
            )
        }
        self.IMPL-QAST-PROCESSORS($context, $qast)
    }

    method IMPL-QAST-PROCESSORS(RakuAST::IMPL::QASTContext $context, Mu $qast) {
        # Non-optimized handling of processors.
        for $!processors {
            if $_ eq 'words' {
                $qast := QAST::Op.new(
                    :op('callmethod'), :name('WORDS_AUTODEREF'), $qast
                );
            }
            elsif $_ eq 'val' {
                my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups);
                $qast := QAST::Op.new(
                    :op('call'), :name(@lookups[0].resolution.lexical-name), $qast
                );
            }
            elsif $_ eq 'exec' {
                $qast := QAST::Op.new(
                    :op('call'), :name('&QX'), $qast
                );
            }
            else {
                nqp::die("Compiling processor '$_' is not implemented");
            }
        }
        $qast
    }

    method visit-children(Code $visitor) {
        my @segments := $!segments;
        for @segments {
            $visitor($_);
        }
    }

    method IMPL-CAN-INTERPRET() {
        nqp::isconcrete(self.literal-value) ?? True !! False
    }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) {
        self.literal-value
    }
}

# An atom in a quote words construct. By wrapping something in this, it is
# considered indivisible in words processing.
class RakuAST::QuoteWordsAtom is RakuAST::Node {
    has RakuAST::Node $.atom;

    method new(RakuAST::Node $atom) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::QuoteWordsAtom, '$!atom', $atom);
        $obj
    }

    method type {
        $!atom.type
    }

    method IMPL-TO-QAST(RakuAST::IMPL::QASTContext $context) {
        $!atom.IMPL-TO-QAST($context)
    }

    method visit-children(Code $visitor) {
        $visitor($!atom)
    }
}
