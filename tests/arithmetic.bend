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
  Q.Rational.Eq(Q.Fraction{Z.ZPos{1n}, 1n}, Q.Fraction{Z.ZPos{2n}, 3n})

def equivalent_fractions():
  {==}

law half_plus_half:
  Q.Rational.Eq(Q.Rational.add(Q.Fraction{Z.ZPos{1n}, 1n}, Q.Fraction{Z.ZPos{1n}, 1n}), Q.Rational.of_nat(1n))

def half_plus_half():
  {==}
