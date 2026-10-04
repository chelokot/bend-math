import Base
import ./Field.bend as K
import ./FieldAlgebra.bend as A
import ./FieldRing.bend as R
import ./Natural.bend as N

def FieldOrder.Lt(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> Type:
  A.Algebra.le(~F, ~field, b, a) -> Empty

def FieldOrder.le_add_both(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, +d: F, ab: A.Algebra.le(~F, ~field, a, b), cd: A.Algebra.le(~F, ~field, c, d)) -> A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, a, c), A.Algebra.add(~F, ~field, b, d)):
  K.Field.le_transitive(F, field)(A.Algebra.add(~F, ~field, a, c), A.Algebra.add(~F, ~field, b, c), A.Algebra.add(~F, ~field, b, d), K.Field.le_add(F, field)(a, b, c, ab),
    A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, c, b), A.Algebra.add(~F, ~field, d, b), A.Algebra.add(~F, ~field, b, c), A.Algebra.add(~F, ~field, b, d), K.Field.le_add(F, field)(c, d, b, cd),
      A.Algebra.add_commutes(~F, ~field, c, b), A.Algebra.add_commutes(~F, ~field, d, b)))

def FieldOrder.le_add_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, ab: A.Algebra.le(~F, ~field, a, b)) -> A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, c, a), A.Algebra.add(~F, ~field, c, b)):
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, a, c), A.Algebra.add(~F, ~field, b, c), A.Algebra.add(~F, ~field, c, a), A.Algebra.add(~F, ~field, c, b), K.Field.le_add(F, field)(a, b, c, ab),
    A.Algebra.add_commutes(~F, ~field, a, c), A.Algebra.add_commutes(~F, ~field, b, c))

def FieldOrder.le_of_same(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, same: A.Algebra.Same(~F, ~field, a, b)) -> A.Algebra.le(~F, ~field, a, b):
  (forward, backward) = same
  forward

def FieldOrder.le_negate(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, ab: A.Algebra.le(~F, ~field, a, b)) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a)):
  +shift: F = A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, b))
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, a, shift), A.Algebra.add(~F, ~field, b, shift), A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a), K.Field.le_add(F, field)(a, b, shift, ab),
    R.FieldRing.equal(~F, ~field, R.Value{a, R.Value{b, R.NoValues{}}},
      R.Plus{R.Variable{0n}, R.Plus{R.Negate{R.Variable{0n}}, R.Negate{R.Variable{1n}}}}, R.Negate{R.Variable{1n}}, {==}),
    R.FieldRing.equal(~F, ~field, R.Value{a, R.Value{b, R.NoValues{}}},
      R.Plus{R.Variable{1n}, R.Plus{R.Negate{R.Variable{0n}}, R.Negate{R.Variable{1n}}}}, R.Negate{R.Variable{0n}}, {==}))

def FieldOrder.zero_le_of_nat(~F: Kind(&2), ~field: K.Field<F>, +n: Nat) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), R.FieldRing.of_nat(~F, ~field, n)):
  match n:
    case 0n:
      K.Field.le_reflexive(F, field)(A.Algebra.zero(~F, ~field))
    case 1n+previous:
      A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field)), A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), R.FieldRing.of_nat(~F, ~field, previous)), A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), R.FieldRing.of_nat(~F, ~field, previous)),
        FieldOrder.le_add_both(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.one(~F, ~field), A.Algebra.zero(~F, ~field), R.FieldRing.of_nat(~F, ~field, previous), K.Field.zero_le_one(F, field), FieldOrder.zero_le_of_nat(~F, ~field, previous)),
        A.Algebra.add_zero(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), R.FieldRing.of_nat(~F, ~field, previous))))

def FieldOrder.of_nat_le_gap(~F: Kind(&2), ~field: K.Field<F>, +a: Nat, +b: Nat, +gap: Nat, gap_is: {Nat.add(a, gap) == b : Nat}) ->
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, b)):
  %gap_is : A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, _))
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), A.Algebra.zero(~F, ~field)), A.Algebra.add(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, gap)),
    R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, Nat.add(a, gap)),
    FieldOrder.le_add_left(~F, ~field, A.Algebra.zero(~F, ~field), R.FieldRing.of_nat(~F, ~field, gap), R.FieldRing.of_nat(~F, ~field, a), FieldOrder.zero_le_of_nat(~F, ~field, gap)),
    A.Algebra.add_zero(~F, ~field, R.FieldRing.of_nat(~F, ~field, a)),
    A.Algebra.same_symmetric(~F, ~field, R.FieldRing.of_nat(~F, ~field, Nat.add(a, gap)), A.Algebra.add(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, gap)),
      R.FieldRing.of_nat_add(~F, ~field, a, gap)))

def FieldOrder.of_nat_le_witness(~F: Kind(&2), ~field: K.Field<F>, +a: Nat, +b: Nat, witness: Exists(Nat, gap => {Nat.add(a, gap) == b : Nat})) ->
  A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, b)):
  (gap, gap_is) = witness
  FieldOrder.of_nat_le_gap(~F, ~field, a, b, gap, gap_is)

def FieldOrder.of_nat_le(~F: Kind(&2), ~field: K.Field<F>, +a: Nat, +b: Nat, ab: N.Natural.Le(a, b)) -> A.Algebra.le(~F, ~field, R.FieldRing.of_nat(~F, ~field, a), R.FieldRing.of_nat(~F, ~field, b)):
  FieldOrder.of_nat_le_witness(~F, ~field, a, b, N.Natural.le_gap(a, b, ab))

def FieldOrder.le_of_lt_order(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, strict: FieldOrder.Lt(~F, ~field, a, b), order: Or(A.Algebra.le(~F, ~field, a, b), A.Algebra.le(~F, ~field, b, a))) -> A.Algebra.le(~F, ~field, a, b):
  match order:
    case Inl{below}:
      below
    case Inr{above}:
      Empty.absurd(A.Algebra.le(~F, ~field, a, b), strict(above))

def FieldOrder.le_of_lt(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, strict: FieldOrder.Lt(~F, ~field, a, b)) -> A.Algebra.le(~F, ~field, a, b):
  FieldOrder.le_of_lt_order(~F, ~field, a, b, strict, K.Field.le_total(F, field)(a, b))
