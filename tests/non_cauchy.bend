import Base
import ../Natural.bend as N
import ../Rational.bend as Q
import ../Real.bend as R

def bad() -> R.Real:
  R.Cauchy{n => Q.Rational.of_nat(n), n => m => N.Natural.zero_le(0n)}
