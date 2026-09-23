import Base
import ./Natural.bend as N
import ./Rational.bend as Q

type Real is Type:
  Cauchy{
    approximate: Nat -> Q.Rational,
    regular: @n: Nat -> @m: Nat -> Q.Rational.Le(Q.Rational.abs(Q.Rational.sub(approximate(n), approximate(m))), Q.Rational.add(Q.Rational.dyadic(n), Q.Rational.dyadic(m)))
  }

def Real.approximate(real: Real, precision: Nat) -> Q.Rational:
  match real:
    case Cauchy{approximate, regular}:
      approximate(precision)

def Real.Eq(x: Real, y: Real) -> Type:
  @precision: Nat -> Q.Rational.Le(Q.Rational.abs(Q.Rational.sub(Real.approximate(x, precision), Real.approximate(y, precision))), Q.Rational.add(Q.Rational.dyadic(precision), Q.Rational.dyadic(precision)))

def Real.zero() -> Real:
  Cauchy{precision => Q.Rational.of_nat(0n), n => m => N.Natural.zero_le(0n)}
