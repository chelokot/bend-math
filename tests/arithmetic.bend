import Base
import ../Integer.bend as Z
import ../Rational.bend as Q

law signed_addition:
  {Z.Integer.add(Z.ZNeg{1n}, Z.ZPos{3n}) == Z.ZPos{1n} : Z.Integer}

def signed_addition():
  {==}

law signed_multiplication:
  {Z.Integer.mul(Z.ZNeg{1n}, Z.ZNeg{2n}) == Z.ZPos{6n} : Z.Integer}

def signed_multiplication():
  {==}

law equivalent_fractions:
  Q.Rational.Eq(Q.Fraction{1n, 0n, 1n}, Q.Fraction{2n, 0n, 3n})

def equivalent_fractions():
  {==}

law half_plus_half:
  Q.Rational.Eq(Q.Rational.add(Q.Fraction{1n, 0n, 1n}, Q.Fraction{1n, 0n, 1n}), Q.Rational.of_nat(1n))

def half_plus_half():
  {==}

law half_plus_negative_half:
  Q.Rational.Eq(Q.Rational.add(Q.Fraction{1n, 0n, 1n}, Q.Fraction{0n, 1n, 1n}), Q.Rational.of_nat(0n))

def half_plus_negative_half():
  {==}

law negative_one_is_less_than_zero:
  Q.Rational.Le(Q.Rational.of_integer(Z.ZNeg{0n}), Q.Rational.of_nat(0n))

def negative_one_is_less_than_zero():
  Unit{}
