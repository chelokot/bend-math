import Base
import ./LAWS.bend as Laws
import ./Natural.bend as N
import ./Integer.bend as Z
import ./Rational.bend as Q
import ./Real.bend as R

def Laws.natural_le_reflexive(n):
  N.Natural.le_reflexive(n)

def Laws.natural_le_transitive(a, b, c, ab, bc):
  N.Natural.le_transitive(a, b, c, ab, bc)

def Laws.natural_le_antisymmetric(a, b, ab, ba):
  N.Natural.le_antisymmetric(a, b, ab, ba)

def Laws.natural_le_add_right(a, b):
  N.Natural.le_add_right(a, b)

def Laws.natural_le_add_both_left(c, a, b, proof):
  N.Natural.le_add_both_left(c, a, b, proof)

def Laws.natural_add_zero(n):
  N.Natural.add_zero(n)

def Laws.natural_add_commutative(a, b):
  N.Natural.add_commutative(a, b)

def Laws.natural_add_associative(a, b, c):
  N.Natural.add_associative(a, b, c)

def Laws.natural_mul_zero(n):
  N.Natural.mul_zero(n)

def Laws.natural_mul_one(n):
  N.Natural.mul_one(n)

def Laws.natural_one_mul(n):
  N.Natural.one_mul(n)

def Laws.natural_mul_add_left(a, b, c):
  N.Natural.mul_add_left(a, b, c)

def Laws.natural_mul_commutative(a, b):
  N.Natural.mul_commutative(a, b)

def Laws.natural_mul_associative(a, b, c):
  N.Natural.mul_associative(a, b, c)

def Laws.natural_mul_add_right(a, b, c):
  N.Natural.mul_add_right(a, b, c)

def Laws.integer_neg_involutive(x):
  Z.Integer.neg_involutive(x)

def Laws.integer_zero_add(x):
  Z.Integer.zero_add(x)

def Laws.integer_add_zero(x):
  Z.Integer.add_zero(x)

def Laws.integer_add_commutative(a, b):
  Z.Integer.add_commutative(a, b)

def Laws.integer_mul_commutative(a, b):
  Z.Integer.mul_commutative(a, b)

def Laws.integer_mul_zero(x):
  Z.Integer.mul_zero(x)

def Laws.integer_zero_mul(x):
  Z.Integer.zero_mul(x)

def Laws.integer_mul_one(x):
  Z.Integer.mul_one(x)

def Laws.integer_one_mul(x):
  Z.Integer.one_mul(x)

def Laws.integer_add_neg_self(x):
  Z.Integer.add_neg_self(x)

def Laws.integer_le_reflexive(x):
  Z.Integer.le_reflexive(x)

def Laws.integer_le_antisymmetric(a, b, ab, ba):
  Z.Integer.le_antisymmetric(a, b, ab, ba)

def Laws.integer_le_transitive(a, b, c, ab, bc):
  Z.Integer.le_transitive(a, b, c, ab, bc)

def Laws.rational_eq_reflexive(x):
  Q.Rational.eq_reflexive(x)

def Laws.rational_eq_symmetric(x, y, proof):
  Q.Rational.eq_symmetric(x, y, proof)

def Laws.rational_neg_involutive(x):
  Q.Rational.neg_involutive(x)

def Laws.rational_eq_negated(x, y, proof):
  Q.Rational.eq_negated(x, y, proof)

def Laws.rational_le_reflexive(x):
  Q.Rational.le_reflexive(x)

def Laws.rational_le_antisymmetric(x, y, xy, yx):
  Q.Rational.le_antisymmetric(x, y, xy, yx)

def Laws.rational_eq_implies_le(x, y, proof):
  Q.Rational.eq_implies_le(x, y, proof)

def Laws.rational_le_negated(x, y, proof):
  Q.Rational.le_negated(x, y, proof)

def Laws.rational_denominator_product(a, b):
  Q.Rational.denominator_product_spec(a, b)

def Laws.real_zero_exists():
  R.Real.zero()

def Laws.real_eq_reflexive(x):
  R.Real.eq_reflexive(x)

def Laws.real_eq_symmetric(x, y, proof):
  R.Real.eq_symmetric(x, y, proof)
