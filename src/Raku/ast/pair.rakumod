# Base role done by things that serve as named arguments.
class RakuAST::NamedArg is RakuAST::Node {
    method named-arg-name() { nqp::die('named-arg-name not implemented') }
    method named-arg-value() { nqp::die('named-arg-value not implemented') }
}

# A fat arrow pair, such as `foo => 42`.
class RakuAST::FatArrow is RakuAST::Term is RakuAST::ImplicitLookups is RakuAST::NamedArg {
    has Str $.key;
    has RakuAST::Term $.value;

    method new(Str :$key!, RakuAST::Term :$value!) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::FatArrow, '$!key', $key);
        nqp::bindattr($obj, RakuAST::FatArrow, '$!value', $value);
        $obj
    }

    method named-arg-name() { $!key }

    method named-arg-value() { $!value }

    method PRODUCE-IMPLICIT-LOOKUPS() {
        self.IMPL-WRAP-LIST([
            RakuAST::Type::Setting.new(RakuAST::Name.from-identifier('Pair')),
        ])
    }

    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups());
        my $pair-type := @lookups[0].resolution.compile-time-value;
        my $key := $!key;
        $context.ensure-sc($key);
        QAST::Op.new(
            :op('callmethod'), :name('new'),
            QAST::WVal.new( :value($pair-type) ),
            QAST::WVal.new( :value($key) ),
            $!value.IMPL-TO-QAST($context)
        )
    }

    method visit-children(Code $visitor) {
        $visitor($!value);
    }
}

# The base of all colonpair constructs.
class RakuAST::ColonPair is RakuAST::Term is RakuAST::ImplicitLookups is RakuAST::NamedArg {
    has Str $.key;
    
    method value() { nqp::die(self.HOW.name(self) ~ ' does not implement value') }

    method named-arg-name() { $!key }

    method named-arg-value() { self.value }

    method PRODUCE-IMPLICIT-LOOKUPS() {
        self.IMPL-WRAP-LIST([
            RakuAST::Type::Setting.new(RakuAST::Name.from-identifier('Pair')),
        ])
    }
    
    method IMPL-EXPR-QAST(RakuAST::IMPL::QASTContext $context) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups());
        my $pair-type := @lookups[0].resolution.compile-time-value;
        my $key := $!key;
        $context.ensure-sc($key);
        QAST::Op.new(
            :op('callmethod'), :name('new'),
            QAST::WVal.new( :value($pair-type) ),
            QAST::WVal.new( :value($key) ),
            self.IMPL-VALUE-QAST($context)
        )
    }

    method IMPL-VALUE-QAST(RakuAST::IMPL::QASTContext $context) {
        self.value.IMPL-TO-QAST($context)
    }
}

# The base of colonpairs that can be placed as adverbs on a quote construct.
class RakuAST::QuotePair is RakuAST::ColonPair {
}

# A truthy colonpair (:foo).
class RakuAST::ColonPair::True is RakuAST::QuotePair {
    method new(Str :$key!) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::ColonPair, '$!key', $key);
        $obj
    }

    method PRODUCE-IMPLICIT-LOOKUPS() {
        self.IMPL-WRAP-LIST([
            RakuAST::Type::Setting.new(RakuAST::Name.from-identifier('Pair'))
        ])
    }

    method value() {
        RakuAST::Declaration::ResolvedConstant.new(compile-time-value => True)
    }

    method simple-compile-time-quote-value() { True }

    method IMPL-VALUE-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := True;
        $context.ensure-sc($value);
        QAST::WVal.new( :$value )
    }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups());
        my $pair-type := @lookups[0].resolution.compile-time-value;
        $pair-type.new(self.key, True)
    }
}

# A falsey colonpair (:!foo).
class RakuAST::ColonPair::False is RakuAST::QuotePair {
    method new(Str :$key!) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::ColonPair, '$!key', $key);
        $obj
    }

    method PRODUCE-IMPLICIT-LOOKUPS() {
        self.IMPL-WRAP-LIST([
            RakuAST::Type::Setting.new(RakuAST::Name.from-identifier('Pair'))
        ])
    }

    method value() {
        RakuAST::Declaration::ResolvedConstant.new(compile-time-value => False),
    }
    
    method simple-compile-time-quote-value() { False }

    method IMPL-VALUE-QAST(RakuAST::IMPL::QASTContext $context) {
        my $value := False;
        $context.ensure-sc($value);
        QAST::WVal.new( :$value )
    }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups());
        my $pair-type := @lookups[0].resolution.compile-time-value;
        $pair-type.new(self.key, False)
    }
}

# A number colonpair (:2th).
class RakuAST::ColonPair::Number is RakuAST::QuotePair {
    has RakuAST::IntLiteral $.value;

    method new(Str :$key!, RakuAST::IntLiteral :$value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::ColonPair, '$!key', $key);
        nqp::bindattr($obj, RakuAST::ColonPair::Number, '$!value', $value);
        $obj
    }

    method simple-compile-time-quote-value() { $!value.value }

    method visit-children(Code $visitor) {
        $visitor($!value);
    }

    method IMPL-CAN-INTERPRET() { True }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups());
        my $pair-type := @lookups[0].resolution.compile-time-value;
        $pair-type.new(self.key, $!value)
    }
}

# A colonpair with a value (:foo(42)).
class RakuAST::ColonPair::Value is RakuAST::QuotePair {
    has RakuAST::Expression $.value;

    method new(Str :$key!, RakuAST::Expression :$value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::ColonPair, '$!key', $key);
        nqp::bindattr($obj, RakuAST::ColonPair::Value, '$!value', $value);
        $obj
    }

    method visit-children(Code $visitor) {
        $visitor($!value);
    }

    method simple-compile-time-quote-value() {
        # TODO various cases we can handle here
        Nil
    }

    method IMPL-CAN-INTERPRET() { $!value.IMPL-CAN-INTERPRET }

    method IMPL-INTERPRET(RakuAST::IMPL::InterpContext $ctx) {
        my @lookups := self.IMPL-UNWRAP-LIST(self.get-implicit-lookups());
        my $pair-type := @lookups[0].resolution.compile-time-value;
        $pair-type.new(self.key, $!value.IMPL-INTERPRET($ctx))
    }
}

# A variable colonpair (:$var, :$<match>).
class RakuAST::ColonPair::Variable is RakuAST::ColonPair {
    has RakuAST::Var $.value;

    method new(Str :$key!, RakuAST::Var :$value) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, RakuAST::ColonPair, '$!key', $key);
        nqp::bindattr($obj, RakuAST::ColonPair::Variable, '$!value', $value);
        $obj
    }

    method visit-children(Code $visitor) {
        $visitor($!value);
    }
}
