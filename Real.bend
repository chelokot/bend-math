import Base
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

def Real.of_rational(+rational: Q.Rational) -> Real:
  Cauchy{
    precision => rational,
    +left_precision => +right_precision =>
      (
        Q.Rational.le_self_add_nonnegative(
          rational,
          Q.Rational.add(Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)),
          Q.Rational.add_nonnegative(
            Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision),
            Q.Rational.dyadic_nonnegative(left_precision),
            Q.Rational.dyadic_nonnegative(right_precision))),
        Q.Rational.le_self_add_nonnegative(
          rational,
          Q.Rational.add(Q.Rational.dyadic(right_precision), Q.Rational.dyadic(left_precision)),
          Q.Rational.add_nonnegative(
            Q.Rational.dyadic(right_precision), Q.Rational.dyadic(left_precision),
            Q.Rational.dyadic_nonnegative(right_precision),
            Q.Rational.dyadic_nonnegative(left_precision)))
      )
  }

def Real.of_rational_close_from_bounds(+a: Q.Rational, +b: Q.Rational, +left_precision: Nat, +right_precision: Nat,
  bounds: Q.Rational.Le(a, b) & Q.Rational.Le(b, a)) ->
  Q.Rational.Close(a, b, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)):
  (forward, backward) = bounds
  (
    Q.Rational.le_transitive(
      a, b,
      Q.Rational.add(b, Q.Rational.add(Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))),
      forward,
      Q.Rational.le_self_add_nonnegative(
        b, Q.Rational.add(Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)),
        Q.Rational.add_nonnegative(
          Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision),
          Q.Rational.dyadic_nonnegative(left_precision),
          Q.Rational.dyadic_nonnegative(right_precision)))),
    Q.Rational.le_transitive(
      b, a,
      Q.Rational.add(a, Q.Rational.add(Q.Rational.dyadic(right_precision), Q.Rational.dyadic(left_precision))),
      backward,
      Q.Rational.le_self_add_nonnegative(
        a, Q.Rational.add(Q.Rational.dyadic(right_precision), Q.Rational.dyadic(left_precision)),
        Q.Rational.add_nonnegative(
          Q.Rational.dyadic(right_precision), Q.Rational.dyadic(left_precision),
          Q.Rational.dyadic_nonnegative(right_precision),
          Q.Rational.dyadic_nonnegative(left_precision))))
  )

def Real.of_rational_eq(+a: Q.Rational, +b: Q.Rational, equality: Q.Rational.Eq(a, b)) ->
  Real.Eq(Real.of_rational(a), Real.of_rational(b)):
  +left_precision => +right_precision =>
    Real.of_rational_close_from_bounds(a, b, left_precision, right_precision,
      Q.Rational.eq_both_le(a, b, equality))

def Real.zero() -> Real:
  Real.of_rational(Q.Rational.zero())
