import Base

type Field<-F: Kind(&2)> is Type:
  Field{
    zero: F,
    one: F,
    half: F,
    add: F -> F -> F,
    neg: F -> F,
    mul: F -> F -> F,
    le: F -> F -> Kind(&2),
    le_reflexive: @+a: F -> le(a, a),
    le_transitive: @+a: F -> @+b: F -> @+c: F -> le(a, b) -> le(b, c) -> le(a, c),
    le_total: @+a: F -> @+b: F -> Or(le(a, b), le(b, a)),
    le_decidable: @+a: F -> @+b: F -> Or(le(a, b), le(a, b) -> Empty),
    le_add: @+a: F -> @+b: F -> @+c: F -> le(a, b) -> le(add(a, c), add(b, c)),
    mul_nonnegative: @+a: F -> @+b: F -> le(zero, a) -> le(zero, b) -> le(zero, mul(a, b)),
    mul_respects: @+a: F -> @+b: F -> @+c: F -> le(a, b) & le(b, a) -> le(mul(a, c), mul(b, c)) & le(mul(b, c), mul(a, c)),
    add_associative: @+a: F -> @+b: F -> @+c: F -> le(add(add(a, b), c), add(a, add(b, c))) & le(add(a, add(b, c)), add(add(a, b), c)),
    add_commutative: @+a: F -> @+b: F -> le(add(a, b), add(b, a)),
    add_zero: @+a: F -> le(add(a, zero), a) & le(a, add(a, zero)),
    add_neg: @+a: F -> le(add(a, neg(a)), zero) & le(zero, add(a, neg(a))),
    mul_associative: @+a: F -> @+b: F -> @+c: F -> le(mul(mul(a, b), c), mul(a, mul(b, c))) & le(mul(a, mul(b, c)), mul(mul(a, b), c)),
    mul_commutative: @+a: F -> @+b: F -> le(mul(a, b), mul(b, a)),
    mul_one: @+a: F -> le(mul(a, one), a) & le(a, mul(a, one)),
    distributive: @+a: F -> @+b: F -> @+c: F -> le(mul(a, add(b, c)), add(mul(a, b), mul(a, c))) & le(add(mul(a, b), mul(a, c)), mul(a, add(b, c))),
    zero_le_one: le(zero, one),
    half_double: le(add(half, half), one) & le(one, add(half, half))
  }

def Field.zero(-F: Kind(&2), field: Field<F>) -> F:
  match field:
    case Field{zero, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      zero

def Field.one(-F: Kind(&2), field: Field<F>) -> F:
  match field:
    case Field{_, one, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      one

def Field.half(-F: Kind(&2), field: Field<F>) -> F:
  match field:
    case Field{_, _, half, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      half

def Field.add(-F: Kind(&2), field: Field<F>) -> F -> F -> F:
  match field:
    case Field{_, _, _, add, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      add

def Field.neg(-F: Kind(&2), field: Field<F>) -> F -> F:
  match field:
    case Field{_, _, _, _, neg, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      neg

def Field.mul(-F: Kind(&2), field: Field<F>) -> F -> F -> F:
  match field:
    case Field{_, _, _, _, _, mul, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      mul

def Field.le(-F: Kind(&2), field: Field<F>) -> F -> F -> Kind(&2):
  match field:
    case Field{_, _, _, _, _, _, le, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      le

def Field.le_reflexive(-F: Kind(&2), field: Field<F>) -> @+a: F -> Field.le(F, field)(a, a):
  match field:
    case Field{_, _, _, _, _, _, _, le_reflexive, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      le_reflexive

def Field.le_transitive(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> @+c: F -> Field.le(F, field)(a, b) -> Field.le(F, field)(b, c) -> Field.le(F, field)(a, c):
  match field:
    case Field{_, _, _, _, _, _, _, _, le_transitive, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      le_transitive

def Field.le_total(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> Or(Field.le(F, field)(a, b), Field.le(F, field)(b, a)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, le_total, _, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      le_total

def Field.le_decidable(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> Or(Field.le(F, field)(a, b), Field.le(F, field)(a, b) -> Empty):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, le_decidable, _, _, _, _, _, _, _, _, _, _, _, _, _}:
      le_decidable

def Field.le_add(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> @+c: F -> Field.le(F, field)(a, b) -> Field.le(F, field)(Field.add(F, field)(a, c), Field.add(F, field)(b, c)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, le_add, _, _, _, _, _, _, _, _, _, _, _, _}:
      le_add

def Field.mul_nonnegative(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> Field.le(F, field)(Field.zero(F, field), a) -> Field.le(F, field)(Field.zero(F, field), b) -> Field.le(F, field)(Field.zero(F, field), Field.mul(F, field)(a, b)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, mul_nonnegative, _, _, _, _, _, _, _, _, _, _, _}:
      mul_nonnegative

def Field.mul_respects(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> @+c: F -> Field.le(F, field)(a, b) & Field.le(F, field)(b, a) -> Field.le(F, field)(Field.mul(F, field)(a, c), Field.mul(F, field)(b, c)) & Field.le(F, field)(Field.mul(F, field)(b, c), Field.mul(F, field)(a, c)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, mul_respects, _, _, _, _, _, _, _, _, _, _}:
      mul_respects

def Field.add_associative(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> @+c: F -> Field.le(F, field)(Field.add(F, field)(Field.add(F, field)(a, b), c), Field.add(F, field)(a, Field.add(F, field)(b, c))) & Field.le(F, field)(Field.add(F, field)(a, Field.add(F, field)(b, c)), Field.add(F, field)(Field.add(F, field)(a, b), c)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, add_associative, _, _, _, _, _, _, _, _, _}:
      add_associative

def Field.add_commutative(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> Field.le(F, field)(Field.add(F, field)(a, b), Field.add(F, field)(b, a)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, add_commutative, _, _, _, _, _, _, _, _}:
      add_commutative

def Field.add_zero(-F: Kind(&2), field: Field<F>) -> @+a: F -> Field.le(F, field)(Field.add(F, field)(a, Field.zero(F, field)), a) & Field.le(F, field)(a, Field.add(F, field)(a, Field.zero(F, field))):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, add_zero, _, _, _, _, _, _, _}:
      add_zero

def Field.add_neg(-F: Kind(&2), field: Field<F>) -> @+a: F -> Field.le(F, field)(Field.add(F, field)(a, Field.neg(F, field)(a)), Field.zero(F, field)) & Field.le(F, field)(Field.zero(F, field), Field.add(F, field)(a, Field.neg(F, field)(a))):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, add_neg, _, _, _, _, _, _}:
      add_neg

def Field.mul_associative(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> @+c: F -> Field.le(F, field)(Field.mul(F, field)(Field.mul(F, field)(a, b), c), Field.mul(F, field)(a, Field.mul(F, field)(b, c))) & Field.le(F, field)(Field.mul(F, field)(a, Field.mul(F, field)(b, c)), Field.mul(F, field)(Field.mul(F, field)(a, b), c)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mul_associative, _, _, _, _, _}:
      mul_associative

def Field.mul_commutative(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> Field.le(F, field)(Field.mul(F, field)(a, b), Field.mul(F, field)(b, a)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mul_commutative, _, _, _, _}:
      mul_commutative

def Field.mul_one(-F: Kind(&2), field: Field<F>) -> @+a: F -> Field.le(F, field)(Field.mul(F, field)(a, Field.one(F, field)), a) & Field.le(F, field)(a, Field.mul(F, field)(a, Field.one(F, field))):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mul_one, _, _, _}:
      mul_one

def Field.distributive(-F: Kind(&2), field: Field<F>) -> @+a: F -> @+b: F -> @+c: F -> Field.le(F, field)(Field.mul(F, field)(a, Field.add(F, field)(b, c)), Field.add(F, field)(Field.mul(F, field)(a, b), Field.mul(F, field)(a, c))) & Field.le(F, field)(Field.add(F, field)(Field.mul(F, field)(a, b), Field.mul(F, field)(a, c)), Field.mul(F, field)(a, Field.add(F, field)(b, c))):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, distributive, _, _}:
      distributive

def Field.zero_le_one(-F: Kind(&2), field: Field<F>) -> Field.le(F, field)(Field.zero(F, field), Field.one(F, field)):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, zero_le_one, _}:
      zero_le_one

def Field.half_double(-F: Kind(&2), field: Field<F>) -> Field.le(F, field)(Field.add(F, field)(Field.half(F, field), Field.half(F, field)), Field.one(F, field)) & Field.le(F, field)(Field.one(F, field), Field.add(F, field)(Field.half(F, field), Field.half(F, field))):
  match field:
    case Field{_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, half_double}:
      half_double
