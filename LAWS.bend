import Base
import ./Natural.bend as N
import ./Integer.bend as Z
import ./Rational.bend as Q
import ./Real.bend as R

law natural_le_reflexive:
  for n: Nat
  N.Natural.Le(n, n)

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

law rational_le_reflexive:
  for x: Q.Rational
  Q.Rational.Le(x, x)

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

law rational_denominator_product:
  for a: Nat
  for b: Nat
  {1n+Q.Rational.denominator_product(a, b) == Nat.mul(1n+a, 1n+b) : Nat}

law real_zero_exists:
  R.Real

law real_eq_reflexive:
  for x: R.Real
  R.Real.Eq(x, x)

law real_eq_symmetric:
  for x: R.Real
  for y: R.Real
  for proof: R.Real.Eq(x, y)
  R.Real.Eq(y, x)
