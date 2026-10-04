import Base
import ./Rational.bend as Q
import ./Field.bend as K
import ./Natural.bend as N

def RationalField.le_decidable(+x: Q.Rational, +y: Q.Rational) -> Or(Q.Rational.Le(x, y), Q.Rational.Le(x, y) -> Empty):
  N.Natural.le_decidable(Q.Rational.left_cross(x, y), Q.Rational.right_cross(x, y))

def RationalField.both_le_of_equal(+x: Q.Rational, +y: Q.Rational, equal: {x == y : Q.Rational}) -> Q.Rational.Le(x, y) & Q.Rational.Le(y, x):
  %equal : Q.Rational.Le(x, _) & Q.Rational.Le(_, x)
  (Q.Rational.le_reflexive(x), Q.Rational.le_reflexive(x))

def RationalField.mul_respects(+a: Q.Rational, +b: Q.Rational, +c: Q.Rational, bounds: Q.Rational.Le(a, b) & Q.Rational.Le(b, a)) ->
  Q.Rational.Le(Q.Rational.mul(a, c), Q.Rational.mul(b, c)) & Q.Rational.Le(Q.Rational.mul(b, c), Q.Rational.mul(a, c)):
  (ab, ba) = bounds
  Q.Rational.eq_both_le(Q.Rational.mul(a, c), Q.Rational.mul(b, c),
    Q.Rational.eq_mul_right(a, b, c, Q.Rational.le_antisymmetric(a, b, ab, ba)))

def RationalField.field() -> K.Field<Q.Rational>:
  K.Field{
    Q.Rational.zero(),
    Q.Rational.one(),
    a => b => Q.Rational.add(a, b),
    a => Q.Rational.neg(a),
    a => b => Q.Rational.mul(a, b),
    +a => +b => Q.Rational.Le(a, b),
    +a => Q.Rational.le_reflexive(a),
    +a => +b => +c => ab => bc => Q.Rational.le_transitive(a, b, c, ab, bc),
    +a => +b => Q.Rational.le_total(a, b),
    +a => +b => RationalField.le_decidable(a, b),
    +a => +b => +c => ab => Q.Rational.le_add_right(a, b, c, ab),
    +a => +b => a_nonnegative => b_nonnegative => Q.Rational.mul_nonnegative(a, b, a_nonnegative, b_nonnegative),
    +a => +b => +c => bounds => RationalField.mul_respects(a, b, c, bounds),
    +a => +b => +c => RationalField.both_le_of_equal(Q.Rational.add(Q.Rational.add(a, b), c), Q.Rational.add(a, Q.Rational.add(b, c)), Q.Rational.add_associative(a, b, c)),
    +a => +b => Pair.fst(Q.Rational.Le(Q.Rational.add(a, b), Q.Rational.add(b, a)), Q.Rational.Le(Q.Rational.add(b, a), Q.Rational.add(a, b)),
      RationalField.both_le_of_equal(Q.Rational.add(a, b), Q.Rational.add(b, a), Q.Rational.add_commutative(a, b))),
    +a => RationalField.both_le_of_equal(Q.Rational.add(a, Q.Rational.zero()), a, Q.Rational.add_zero(a)),
    +a => Q.Rational.eq_both_le(Q.Rational.add(a, Q.Rational.neg(a)), Q.Rational.zero(), Q.Rational.add_neg_self(a)),
    +a => +b => +c => RationalField.both_le_of_equal(Q.Rational.mul(Q.Rational.mul(a, b), c), Q.Rational.mul(a, Q.Rational.mul(b, c)), Q.Rational.mul_associative(a, b, c)),
    +a => +b => Pair.fst(Q.Rational.Le(Q.Rational.mul(a, b), Q.Rational.mul(b, a)), Q.Rational.Le(Q.Rational.mul(b, a), Q.Rational.mul(a, b)),
      RationalField.both_le_of_equal(Q.Rational.mul(a, b), Q.Rational.mul(b, a), Q.Rational.mul_commutative(a, b))),
    +a => RationalField.both_le_of_equal(Q.Rational.mul(a, Q.Rational.one()), a, Q.Rational.mul_one(a)),
    +a => +b => +c => Q.Rational.eq_both_le(Q.Rational.mul(a, Q.Rational.add(b, c)), Q.Rational.add(Q.Rational.mul(a, b), Q.Rational.mul(a, c)), Q.Rational.mul_add_distributive(a, b, c)),
    Unit{}
  }
