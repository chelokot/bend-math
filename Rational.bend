import Base
import ./Natural.bend as N
import ./Integer.bend as Z

type Rational is Data:
  Fraction{numerator: Z.Integer, denominator_predecessor: Nat}

def Rational.of_integer(x: Z.Integer) -> Rational:
  Fraction{x, 0n}

def Rational.of_nat(n: Nat) -> Rational:
  Fraction{Z.Integer.of_nat(n), 0n}

def Rational.numerator(x: Rational) -> Z.Integer:
  match x:
    case Fraction{numerator, denominator_predecessor}:
      numerator

def Rational.denominator(x: Rational) -> Z.Integer:
  match x:
    case Fraction{numerator, denominator_predecessor}:
      Z.Integer.of_nat(1n+denominator_predecessor)

def Rational.denominator_product(a: Nat, +b: Nat) -> Nat:
  Nat.add(b, Nat.mul(a, 1n+b))

def Rational.denominator_product_spec(a: Nat, +b: Nat) -> {1n+Rational.denominator_product(a, b) == Nat.mul(1n+a, 1n+b) : Nat}:
  {==}

def Rational.add(a: Rational, b: Rational) -> Rational:
  match a b:
    case Fraction{an, +ad} Fraction{bn, +bd}:
      Fraction{Z.Integer.add(Z.Integer.mul(an, Z.Integer.of_nat(1n+bd)), Z.Integer.mul(bn, Z.Integer.of_nat(1n+ad))), Rational.denominator_product(ad, bd)}

def Rational.neg(x: Rational) -> Rational:
  match x:
    case Fraction{numerator, denominator_predecessor}:
      Fraction{Z.Integer.neg(numerator), denominator_predecessor}

def Rational.abs(x: Rational) -> Rational:
  match x:
    case Fraction{numerator, denominator_predecessor}:
      Fraction{Z.Integer.abs(numerator), denominator_predecessor}

def Rational.sub(a: Rational, b: Rational) -> Rational:
  Rational.add(a, Rational.neg(b))

def Rational.mul(a: Rational, b: Rational) -> Rational:
  match a b:
    case Fraction{an, ad} Fraction{bn, bd}:
      Fraction{Z.Integer.mul(an, bn), Rational.denominator_product(ad, bd)}

def Rational.cross(x: Rational, y: Rational) -> Z.Integer:
  Z.Integer.mul(Rational.numerator(x), Rational.denominator(y))

def Rational.Eq(+x: Rational, +y: Rational) -> Type:
  {Rational.cross(x, y) == Rational.cross(y, x) : Z.Integer}

def Rational.Le(+x: Rational, +y: Rational) -> Type:
  Z.Integer.Le(Rational.cross(x, y), Rational.cross(y, x))

def Rational.Close(+x: Rational, +y: Rational, +left_error: Rational, +right_error: Rational) -> Type:
  Rational.Le(x, Rational.add(y, Rational.add(left_error, right_error))) & Rational.Le(y, Rational.add(x, Rational.add(right_error, left_error)))

def Rational.close_symmetric(+x: Rational, +y: Rational, +left_error: Rational, +right_error: Rational, proof: Rational.Close(x, y, left_error, right_error)) -> Rational.Close(y, x, right_error, left_error):
  (forward, backward) = proof
  (backward, forward)

def Rational.eq_reflexive(x: Rational) -> Rational.Eq(x, x):
  {==}

def Rational.eq_symmetric(+x: Rational, +y: Rational, proof: Rational.Eq(x, y)) -> Rational.Eq(y, x):
  Equal.sym(Z.Integer, Rational.cross(x, y), Rational.cross(y, x), proof)

def Rational.le_reflexive(+x: Rational) -> Rational.Le(x, x):
  Z.Integer.le_reflexive(Rational.cross(x, x))

def Rational.le_antisymmetric(+x: Rational, +y: Rational, xy: Rational.Le(x, y), yx: Rational.Le(y, x)) -> Rational.Eq(x, y):
  Z.Integer.le_antisymmetric(Rational.cross(x, y), Rational.cross(y, x), xy, yx)

def Rational.eq_implies_le(+x: Rational, +y: Rational, proof: Rational.Eq(x, y)) -> Rational.Le(x, y):
  %proof : Z.Integer.Le(Rational.cross(x, y), _)
  Z.Integer.le_reflexive(Rational.cross(x, y))

def Rational.two_power_predecessor(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+Nat.double(Rational.two_power_predecessor(p))

def Rational.dyadic(n: Nat) -> Rational:
  Fraction{Z.Integer.one(), Rational.two_power_predecessor(n)}
