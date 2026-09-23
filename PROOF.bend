import Base
import ./LAWS.bend as Laws
import ./Natural.bend as N
import ./Integer.bend as Z
import ./Rational.bend as Q
import ./Real.bend as R

def Laws.natural_le_reflexive(n):
  N.Natural.le_reflexive(n)

def Laws.natural_le_total(a, b):
  N.Natural.le_total(a, b)

def Laws.natural_le_transitive(a, b, c, ab, bc):
  N.Natural.le_transitive(a, b, c, ab, bc)

def Laws.natural_le_antisymmetric(a, b, ab, ba):
  N.Natural.le_antisymmetric(a, b, ab, ba)

def Laws.natural_le_has_gap(a, b, proof):
  N.Natural.le_gap(a, b, proof)

def Laws.natural_le_from_gap(a, b, gap, equality):
  N.Natural.le_from_gap(a, b, gap, equality)

def Laws.natural_le_mul_right(a, b, c, proof):
  N.Natural.le_mul_right(a, b, c, proof)

def Laws.natural_le_mul_left(a, b, c, proof):
  N.Natural.le_mul_left(a, b, c, proof)

def Laws.natural_le_mul_right_cancel_positive(k, a, b, proof):
  N.Natural.le_mul_right_cancel_positive(k, a, b, proof)

def Laws.natural_le_mul_left_cancel_positive(k, a, b, proof):
  N.Natural.le_mul_left_cancel_positive(k, a, b, proof)

def Laws.natural_le_balance(a, b, c, d, e, f, first, second):
  N.Natural.le_balance(a, b, c, d, e, f, first, second)

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

def Laws.natural_double_add(n):
  N.Natural.double_add(n)

def Laws.natural_add_left_cancel(c, a, b, proof):
  N.Natural.add_left_cancel(c, a, b, proof)

def Laws.natural_add_right_cancel(a, b, c, proof):
  N.Natural.add_right_cancel(a, b, c, proof)

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

def Laws.natural_mul_right_cancel_positive(k, a, b, proof):
  N.Natural.mul_right_cancel_positive(k, a, b, proof)

def Laws.natural_mul_left_cancel_positive(k, a, b, proof):
  N.Natural.mul_left_cancel_positive(k, a, b, proof)

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

def Laws.integer_subtract_spec(a, b):
  Z.Integer.subtract_spec(a, b)

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

def Laws.rational_eq_transitive(x, y, z, xy, yz):
  Q.Rational.eq_transitive(x, y, z, xy, yz)

def Laws.rational_neg_involutive(x):
  Q.Rational.neg_involutive(x)

def Laws.rational_eq_negated(x, y, proof):
  Q.Rational.eq_negated(x, y, proof)

def Laws.rational_le_reflexive(x):
  Q.Rational.le_reflexive(x)

def Laws.rational_le_total(x, y):
  Q.Rational.le_total(x, y)

def Laws.rational_mul_nonnegative(x, y, x_nonnegative, y_nonnegative):
  Q.Rational.mul_nonnegative(x, y, x_nonnegative, y_nonnegative)

def Laws.rational_add_nonnegative(x, y, x_nonnegative, y_nonnegative):
  Q.Rational.add_nonnegative(x, y, x_nonnegative, y_nonnegative)

def Laws.rational_zero_ne_one(proof):
  Q.Rational.zero_ne_one(proof)

def Laws.rational_le_transitive(x, y, z, xy, yz):
  Q.Rational.le_transitive(x, y, z, xy, yz)

def Laws.rational_le_respects_equality(x, x_replacement, y, y_replacement, x_equal, y_equal, xy):
  Q.Rational.le_replace(x, x_replacement, y, y_replacement, x_equal, y_equal, xy)

def Laws.rational_le_add_right(x, y, z, xy):
  Q.Rational.le_add_right(x, y, z, xy)

def Laws.rational_add_respects_equality(x, x_replacement, y, y_replacement, x_equal, y_equal):
  Q.Rational.eq_add_both(x, x_replacement, y, y_replacement, x_equal, y_equal)

def Laws.rational_mul_respects_equality(x, x_replacement, y, y_replacement, x_equal, y_equal):
  Q.Rational.eq_mul_both(x, x_replacement, y, y_replacement, x_equal, y_equal)

def Laws.rational_scale_preserves_equality(x, factor_predecessor):
  Q.Rational.scale_preserves_eq(x, factor_predecessor)

def Laws.rational_mul_add_distributive(a, b, c):
  Q.Rational.mul_add_distributive(a, b, c)

def Laws.rational_add_mul_distributive(a, b, c):
  Q.Rational.add_mul_distributive(a, b, c)

def Laws.rational_inverse_cancel(x, nonzero):
  Q.Rational.inverse_cancel(x, nonzero)

def Laws.rational_inverse_unique(x, u, v, xu, xv):
  Q.Rational.inverse_unique(x, u, v, xu, xv)

def Laws.rational_inverse_respects_nonzero_equality(x, y, equality, x_nonzero, y_nonzero):
  Q.Rational.inverse_respects_nonzero_eq(x, y, equality, x_nonzero, y_nonzero)

def Laws.rational_inverse_respects_equality(x, y, equality):
  Q.Rational.inverse_respects_eq(x, y, equality)

def Laws.rational_le_antisymmetric(x, y, xy, yx):
  Q.Rational.le_antisymmetric(x, y, xy, yx)

def Laws.rational_eq_implies_le(x, y, proof):
  Q.Rational.eq_implies_le(x, y, proof)

def Laws.rational_le_negated(x, y, proof):
  Q.Rational.le_negated(x, y, proof)

def Laws.rational_denominator_product(a, b):
  Q.Rational.denominator_product_spec(a, b)

def Laws.rational_add_commutative(a, b):
  Q.Rational.add_commutative(a, b)

def Laws.rational_add_associative(a, b, c):
  Q.Rational.add_associative(a, b, c)

def Laws.rational_mul_commutative(a, b):
  Q.Rational.mul_commutative(a, b)

def Laws.rational_mul_associative(a, b, c):
  Q.Rational.mul_associative(a, b, c)

def Laws.rational_add_zero(x):
  Q.Rational.add_zero(x)

def Laws.rational_zero_add(x):
  Q.Rational.zero_add(x)

def Laws.rational_mul_one(x):
  Q.Rational.mul_one(x)

def Laws.rational_one_mul(x):
  Q.Rational.one_mul(x)

def Laws.rational_add_neg_self(x):
  Q.Rational.add_neg_self(x)

def Laws.rational_mul_zero(x):
  Q.Rational.mul_zero(x)

def Laws.rational_dyadic_nonnegative(n):
  Q.Rational.dyadic_nonnegative(n)

def Laws.rational_dyadic_denominator_doubles(n):
  Q.Rational.dyadic_denominator_next(n)

def Laws.rational_dyadic_double(n):
  Q.Rational.dyadic_double(n)

def Laws.rational_close_add_same_errors(a, b, c, d, left_error, right_error, first, second):
  Q.Rational.close_add_same_errors(a, b, c, d, left_error, right_error, first, second)

def Laws.rational_close_halve_errors(x, y, n, m, proof):
  Q.Rational.close_halve_errors(x, y, n, m, proof)

def Laws.real_zero_exists():
  R.Real.zero()

def Laws.real_rational_embedding(rational):
  R.Real.of_rational(rational)

def Laws.real_rational_embedding_respects_equality(a, b, equality):
  R.Real.of_rational_eq(a, b, equality)

def Laws.real_eq_reflexive(x):
  R.Real.eq_reflexive(x)

def Laws.real_eq_symmetric(x, y, proof):
  R.Real.eq_symmetric(x, y, proof)
