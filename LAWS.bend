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

law integer_neg_involutive:
  for x: Z.Integer
  {Z.Integer.neg(Z.Integer.neg(x)) == x : Z.Integer}

law integer_zero_add:
  for x: Z.Integer
  {Z.Integer.add(Z.Integer.zero(), x) == x : Z.Integer}

law integer_add_zero:
  for x: Z.Integer
  {Z.Integer.add(x, Z.Integer.zero()) == x : Z.Integer}

law integer_le_reflexive:
  for x: Z.Integer
  Z.Integer.Le(x, x)

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
