import Base
import ./Natural.bend as N
import ./Integer.bend as Z
import ./Rational.bend as Q
import ./Real.bend as R

law natural_le_reflexive:
  for n: Nat
  N.Natural.Le(n, n)

law natural_le_total:
  for a: Nat
  for b: Nat
  Or(N.Natural.Le(a, b), N.Natural.Le(b, a))

law natural_le_transitive:
  for a: Nat
  for b: Nat
  for c: Nat
  for ab: N.Natural.Le(a, b)
  for bc: N.Natural.Le(b, c)
  N.Natural.Le(a, c)

law natural_le_antisymmetric:
  for a: Nat
  for b: Nat
  for ab: N.Natural.Le(a, b)
  for ba: N.Natural.Le(b, a)
  {a == b : Nat}

law natural_le_has_gap:
  for a: Nat
  for b: Nat
  for proof: N.Natural.Le(a, b)
  exs gap: Nat
  {Nat.add(a, gap) == b : Nat}

law natural_le_from_gap:
  for a: Nat
  for b: Nat
  for gap: Nat
  for equality: {Nat.add(a, gap) == b : Nat}
  N.Natural.Le(a, b)

law natural_le_mul_right:
  for a: Nat
  for b: Nat
  for c: Nat
  for proof: N.Natural.Le(a, b)
  N.Natural.Le(Nat.mul(a, c), Nat.mul(b, c))

law natural_le_mul_left:
  for a: Nat
  for b: Nat
  for c: Nat
  for proof: N.Natural.Le(a, b)
  N.Natural.Le(Nat.mul(c, a), Nat.mul(c, b))

law natural_le_mul_right_cancel_positive:
  for k: Nat
  for a: Nat
  for b: Nat
  for proof: N.Natural.Le(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))
  N.Natural.Le(a, b)

law natural_le_mul_left_cancel_positive:
  for k: Nat
  for a: Nat
  for b: Nat
  for proof: N.Natural.Le(Nat.mul(1n+k, a), Nat.mul(1n+k, b))
  N.Natural.Le(a, b)

law natural_le_balance:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  for e: Nat
  for f: Nat
  for first: N.Natural.Le(Nat.add(a, c), Nat.add(b, d))
  for second: N.Natural.Le(Nat.add(b, e), Nat.add(c, f))
  N.Natural.Le(Nat.add(a, e), Nat.add(d, f))

law natural_le_add_right:
  for a: Nat
  for b: Nat
  N.Natural.Le(a, Nat.add(a, b))

law natural_le_add_both_left:
  for c: Nat
  for a: Nat
  for b: Nat
  for proof: N.Natural.Le(a, b)
  N.Natural.Le(Nat.add(c, a), Nat.add(c, b))

law natural_add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

law natural_add_commutative:
  for a: Nat
  for b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

law natural_add_associative:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

law natural_double_add:
  for n: Nat
  {Nat.double(n) == Nat.add(n, n) : Nat}

law natural_add_left_cancel:
  for c: Nat
  for a: Nat
  for b: Nat
  for proof: {Nat.add(c, a) == Nat.add(c, b) : Nat}
  {a == b : Nat}

law natural_add_right_cancel:
  for a: Nat
  for b: Nat
  for c: Nat
  for proof: {Nat.add(a, c) == Nat.add(b, c) : Nat}
  {a == b : Nat}

law natural_mul_zero:
  for n: Nat
  {Nat.mul(n, 0n) == 0n : Nat}

law natural_mul_one:
  for n: Nat
  {Nat.mul(n, 1n) == n : Nat}

law natural_one_mul:
  for n: Nat
  {Nat.mul(1n, n) == n : Nat}

law natural_mul_add_left:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

law natural_mul_commutative:
  for a: Nat
  for b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

law natural_mul_associative:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

law natural_mul_add_right:
  for a: Nat
  for b: Nat
  for c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

law natural_mul_right_cancel_positive:
  for k: Nat
  for a: Nat
  for b: Nat
  for proof: {Nat.mul(a, 1n+k) == Nat.mul(b, 1n+k) : Nat}
  {a == b : Nat}

law natural_mul_left_cancel_positive:
  for k: Nat
  for a: Nat
  for b: Nat
  for proof: {Nat.mul(1n+k, a) == Nat.mul(1n+k, b) : Nat}
  {a == b : Nat}

law integer_neg_involutive:
  for x: Z.Integer
  {Z.Integer.neg(Z.Integer.neg(x)) == x : Z.Integer}

law integer_zero_add:
  for x: Z.Integer
  {Z.Integer.add(Z.Integer.zero(), x) == x : Z.Integer}

law integer_add_zero:
  for x: Z.Integer
  {Z.Integer.add(x, Z.Integer.zero()) == x : Z.Integer}

law integer_add_commutative:
  for a: Z.Integer
  for b: Z.Integer
  {Z.Integer.add(a, b) == Z.Integer.add(b, a) : Z.Integer}

law integer_mul_commutative:
  for a: Z.Integer
  for b: Z.Integer
  {Z.Integer.mul(a, b) == Z.Integer.mul(b, a) : Z.Integer}

law integer_mul_zero:
  for x: Z.Integer
  {Z.Integer.mul(x, Z.Integer.zero()) == Z.Integer.zero() : Z.Integer}

law integer_zero_mul:
  for x: Z.Integer
  {Z.Integer.mul(Z.Integer.zero(), x) == Z.Integer.zero() : Z.Integer}

law integer_mul_one:
  for x: Z.Integer
  {Z.Integer.mul(x, Z.Integer.one()) == x : Z.Integer}

law integer_one_mul:
  for x: Z.Integer
  {Z.Integer.mul(Z.Integer.one(), x) == x : Z.Integer}

law integer_add_neg_self:
  for x: Z.Integer
  {Z.Integer.add(x, Z.Integer.neg(x)) == Z.Integer.zero() : Z.Integer}

law integer_subtract_spec:
  for a: Nat
  for b: Nat
  Z.Integer.SubtractSpec(a, b, Z.Integer.subtract_naturals(a, b))

law integer_le_reflexive:
  for x: Z.Integer
  Z.Integer.Le(x, x)

law integer_le_antisymmetric:
  for a: Z.Integer
  for b: Z.Integer
  for ab: Z.Integer.Le(a, b)
  for ba: Z.Integer.Le(b, a)
  {a == b : Z.Integer}

law integer_le_transitive:
  for a: Z.Integer
  for b: Z.Integer
  for c: Z.Integer
  for ab: Z.Integer.Le(a, b)
  for bc: Z.Integer.Le(b, c)
  Z.Integer.Le(a, c)

law rational_eq_reflexive:
  for x: Q.Rational
  Q.Rational.Eq(x, x)

law rational_eq_symmetric:
  for x: Q.Rational
  for y: Q.Rational
  for proof: Q.Rational.Eq(x, y)
  Q.Rational.Eq(y, x)

law rational_eq_transitive:
  for x: Q.Rational
  for y: Q.Rational
  for z: Q.Rational
  for xy: Q.Rational.Eq(x, y)
  for yz: Q.Rational.Eq(y, z)
  Q.Rational.Eq(x, z)

law rational_neg_involutive:
  for x: Q.Rational
  {Q.Rational.neg(Q.Rational.neg(x)) == x : Q.Rational}

law rational_eq_negated:
  for x: Q.Rational
  for y: Q.Rational
  for proof: Q.Rational.Eq(x, y)
  Q.Rational.Eq(Q.Rational.neg(x), Q.Rational.neg(y))

law rational_le_reflexive:
  for x: Q.Rational
  Q.Rational.Le(x, x)

law rational_le_total:
  for x: Q.Rational
  for y: Q.Rational
  Or(Q.Rational.Le(x, y), Q.Rational.Le(y, x))

law rational_mul_nonnegative:
  for x: Q.Rational
  for y: Q.Rational
  for x_nonnegative: Q.Rational.Le(Q.Rational.zero(), x)
  for y_nonnegative: Q.Rational.Le(Q.Rational.zero(), y)
  Q.Rational.Le(Q.Rational.zero(), Q.Rational.mul(x, y))

law rational_add_nonnegative:
  for x: Q.Rational
  for y: Q.Rational
  for x_nonnegative: Q.Rational.Le(Q.Rational.zero(), x)
  for y_nonnegative: Q.Rational.Le(Q.Rational.zero(), y)
  Q.Rational.Le(Q.Rational.zero(), Q.Rational.add(x, y))

law rational_zero_ne_one:
  Q.Rational.Eq(Q.Rational.zero(), Q.Rational.one()) -> Empty

law rational_le_transitive:
  for x: Q.Rational
  for y: Q.Rational
  for z: Q.Rational
  for xy: Q.Rational.Le(x, y)
  for yz: Q.Rational.Le(y, z)
  Q.Rational.Le(x, z)

law rational_le_respects_equality:
  for x: Q.Rational
  for x_replacement: Q.Rational
  for y: Q.Rational
  for y_replacement: Q.Rational
  for x_equal: Q.Rational.Eq(x, x_replacement)
  for y_equal: Q.Rational.Eq(y, y_replacement)
  for xy: Q.Rational.Le(x, y)
  Q.Rational.Le(x_replacement, y_replacement)

law rational_le_add_right:
  for x: Q.Rational
  for y: Q.Rational
  for z: Q.Rational
  for xy: Q.Rational.Le(x, y)
  Q.Rational.Le(Q.Rational.add(x, z), Q.Rational.add(y, z))

law rational_add_respects_equality:
  for x: Q.Rational
  for x_replacement: Q.Rational
  for y: Q.Rational
  for y_replacement: Q.Rational
  for x_equal: Q.Rational.Eq(x, x_replacement)
  for y_equal: Q.Rational.Eq(y, y_replacement)
  Q.Rational.Eq(Q.Rational.add(x, y), Q.Rational.add(x_replacement, y_replacement))

law rational_mul_respects_equality:
  for x: Q.Rational
  for x_replacement: Q.Rational
  for y: Q.Rational
  for y_replacement: Q.Rational
  for x_equal: Q.Rational.Eq(x, x_replacement)
  for y_equal: Q.Rational.Eq(y, y_replacement)
  Q.Rational.Eq(Q.Rational.mul(x, y), Q.Rational.mul(x_replacement, y_replacement))

law rational_scale_preserves_equality:
  for x: Q.Rational
  for factor_predecessor: Nat
  Q.Rational.Eq(x, Q.Rational.scale(x, factor_predecessor))

law rational_mul_add_distributive:
  for a: Q.Rational
  for b: Q.Rational
  for c: Q.Rational
  Q.Rational.Eq(Q.Rational.mul(a, Q.Rational.add(b, c)), Q.Rational.add(Q.Rational.mul(a, b), Q.Rational.mul(a, c)))

law rational_add_mul_distributive:
  for a: Q.Rational
  for b: Q.Rational
  for c: Q.Rational
  Q.Rational.Eq(Q.Rational.mul(Q.Rational.add(a, b), c), Q.Rational.add(Q.Rational.mul(a, c), Q.Rational.mul(b, c)))

law rational_inverse_cancel:
  for x: Q.Rational
  for nonzero: Q.Rational.Eq(x, Q.Rational.zero()) -> Empty
  Q.Rational.Eq(Q.Rational.mul(x, Q.Rational.inverse(x)), Q.Rational.one())

law rational_inverse_unique:
  for x: Q.Rational
  for u: Q.Rational
  for v: Q.Rational
  for xu: Q.Rational.Eq(Q.Rational.mul(x, u), Q.Rational.one())
  for xv: Q.Rational.Eq(Q.Rational.mul(x, v), Q.Rational.one())
  Q.Rational.Eq(u, v)

law rational_inverse_respects_nonzero_equality:
  for x: Q.Rational
  for y: Q.Rational
  for equality: Q.Rational.Eq(x, y)
  for x_nonzero: Q.Rational.Eq(x, Q.Rational.zero()) -> Empty
  for y_nonzero: Q.Rational.Eq(y, Q.Rational.zero()) -> Empty
  Q.Rational.Eq(Q.Rational.inverse(x), Q.Rational.inverse(y))

law rational_inverse_respects_equality:
  for x: Q.Rational
  for y: Q.Rational
  for equality: Q.Rational.Eq(x, y)
  Q.Rational.Eq(Q.Rational.inverse(x), Q.Rational.inverse(y))

law rational_le_antisymmetric:
  for x: Q.Rational
  for y: Q.Rational
  for xy: Q.Rational.Le(x, y)
  for yx: Q.Rational.Le(y, x)
  Q.Rational.Eq(x, y)

law rational_eq_implies_le:
  for x: Q.Rational
  for y: Q.Rational
  for proof: Q.Rational.Eq(x, y)
  Q.Rational.Le(x, y)

law rational_le_negated:
  for x: Q.Rational
  for y: Q.Rational
  for proof: Q.Rational.Le(x, y)
  Q.Rational.Le(Q.Rational.neg(y), Q.Rational.neg(x))

law rational_denominator_product:
  for a: Nat
  for b: Nat
  {1n+Q.Rational.denominator_product(a, b) == Nat.mul(1n+a, 1n+b) : Nat}

law rational_add_commutative:
  for a: Q.Rational
  for b: Q.Rational
  {Q.Rational.add(a, b) == Q.Rational.add(b, a) : Q.Rational}

law rational_add_associative:
  for a: Q.Rational
  for b: Q.Rational
  for c: Q.Rational
  {Q.Rational.add(Q.Rational.add(a, b), c) == Q.Rational.add(a, Q.Rational.add(b, c)) : Q.Rational}

law rational_mul_commutative:
  for a: Q.Rational
  for b: Q.Rational
  {Q.Rational.mul(a, b) == Q.Rational.mul(b, a) : Q.Rational}

law rational_mul_associative:
  for a: Q.Rational
  for b: Q.Rational
  for c: Q.Rational
  {Q.Rational.mul(Q.Rational.mul(a, b), c) == Q.Rational.mul(a, Q.Rational.mul(b, c)) : Q.Rational}

law rational_add_zero:
  for x: Q.Rational
  {Q.Rational.add(x, Q.Rational.zero()) == x : Q.Rational}

law rational_zero_add:
  for x: Q.Rational
  {Q.Rational.add(Q.Rational.zero(), x) == x : Q.Rational}

law rational_mul_one:
  for x: Q.Rational
  {Q.Rational.mul(x, Q.Rational.one()) == x : Q.Rational}

law rational_one_mul:
  for x: Q.Rational
  {Q.Rational.mul(Q.Rational.one(), x) == x : Q.Rational}

law rational_add_neg_self:
  for x: Q.Rational
  Q.Rational.Eq(Q.Rational.add(x, Q.Rational.neg(x)), Q.Rational.zero())

law rational_mul_zero:
  for x: Q.Rational
  Q.Rational.Eq(Q.Rational.mul(x, Q.Rational.zero()), Q.Rational.zero())

law rational_dyadic_nonnegative:
  for n: Nat
  Q.Rational.Le(Q.Rational.zero(), Q.Rational.dyadic(n))

law rational_dyadic_denominator_doubles:
  for n: Nat
  {Q.Rational.denominator(Q.Rational.dyadic(1n+n)) ==
   Nat.add(Q.Rational.denominator(Q.Rational.dyadic(n)), Q.Rational.denominator(Q.Rational.dyadic(n))) : Nat}

law real_zero_exists:
  R.Real

law real_rational_embedding:
  for rational: Q.Rational
  R.Real

law real_rational_embedding_respects_equality:
  for a: Q.Rational
  for b: Q.Rational
  for equality: Q.Rational.Eq(a, b)
  R.Real.Eq(R.Real.of_rational(a), R.Real.of_rational(b))

law real_eq_reflexive:
  for x: R.Real
  R.Real.Eq(x, x)

law real_eq_symmetric:
  for x: R.Real
  for y: R.Real
  for proof: R.Real.Eq(x, y)
  R.Real.Eq(y, x)
