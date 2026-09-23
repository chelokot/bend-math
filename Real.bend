import Base
import ./Natural.bend as N
import ./Rational.bend as Q

type Real is Type:
  Cauchy{
    approximate: Nat -> Q.Rational,
    regular: @n: Nat -> @m: Nat -> Q.Rational.Close(approximate(n), approximate(m), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
  }

def Real.approximate(real: Real, precision: Nat) -> Q.Rational:
  match real:
    case Cauchy{approximate, regular}:
      approximate(precision)

def Real.Eq(x: Real, y: Real) -> Type:
  @left_precision: Nat -> @right_precision: Nat -> Q.Rational.Close(Real.approximate(x, left_precision), Real.approximate(y, right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))

def Real.eq_reflexive(x: Real) -> Real.Eq(x, x):
  match x:
    case Cauchy{approximate, regular}:
      regular

def Real.eq_symmetric(x: Real, y: Real, proof: Real.Eq(x, y)) -> Real.Eq(y, x):
  +right_precision => +left_precision =>
    Q.Rational.close_symmetric(Real.approximate(x, left_precision), Real.approximate(y, right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision), proof(left_precision)(right_precision))

def Real.zero() -> Real:
  Cauchy{precision => Q.Rational.of_nat(0n), n => m => (N.Natural.zero_le(0n), N.Natural.zero_le(0n))}
