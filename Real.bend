import Base
import ./Rational.bend as Q

type Real.Sample<-approximate: Nat -> Q.Rational, -left_precision: Nat, -right_precision: Nat> is Type:
  Sample{
    left: Q.Rational,
    right: Q.Rational,
    left_is: {left == approximate(left_precision) : Q.Rational},
    right_is: {right == approximate(right_precision) : Q.Rational},
    close: Q.Rational.Close(left, right, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
  }

type Real is Type:
  Cauchy{
    approximate: Nat -> Q.Rational,
    regular: @n: Nat -> @m: Nat -> Real.Sample<approximate, n, m>
  }

def Real.approximations(real: Real) -> Nat -> Q.Rational:
  match real:
    case Cauchy{approximate, regular}:
      approximate

def Real.approximate(real: Real, +precision: Nat) -> Q.Rational:
  Real.approximations(real)(precision)

def Real.Eq(x: Real, y: Real) -> Type:
  @left_precision: Nat -> @right_precision: Nat -> Q.Rational.Close(Real.approximate(x, left_precision), Real.approximate(y, right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))

def Real.sample_close(-approximate: Nat -> Q.Rational, +left_precision: Nat, +right_precision: Nat,
  sample: Real.Sample<approximate, left_precision, right_precision>) ->
  Q.Rational.Close(approximate(left_precision), approximate(right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)):
  match sample:
    case Sample{+left, +right, left_is, right_is, close}:
      %left_is : Q.Rational.Close(_, approximate(right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %right_is : Q.Rational.Close(left, _, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      close

def Real.eq_reflexive(x: Real) -> Real.Eq(x, x):
  match x:
    case Cauchy{approximate, regular}:
      +left_precision => +right_precision =>
        Real.sample_close(approximate, left_precision, right_precision, regular(left_precision)(right_precision))

def Real.eq_symmetric(x: Real, y: Real, proof: Real.Eq(x, y)) -> Real.Eq(y, x):
  +right_precision => +left_precision =>
    Q.Rational.close_symmetric(Real.approximate(x, left_precision), Real.approximate(y, right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision), proof(left_precision)(right_precision))

def Real.eq_transitive(x: Real, y: Real, z: Real, xy: Real.Eq(x, y), yz: Real.Eq(y, z)) -> Real.Eq(x, z):
  +left_precision => +right_precision =>
    Q.Rational.close_transitive_dyadic(
      Real.approximate(x, left_precision), Real.approximate(z, right_precision),
      left_precision, right_precision, Real.approximations(y),
      xy(left_precision), +middle_precision => yz(middle_precision)(right_precision))

def Real.of_rational(+rational: Q.Rational) -> Real:
  Cauchy{
    precision => rational,
    +left_precision => +right_precision =>
      Sample{rational, rational, {==}, {==},
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
        )}
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

def Real.add_approximations(x: Nat -> Q.Rational, y: Nat -> Q.Rational) -> Nat -> Q.Rational:
  +precision => Q.Rational.add(x(1n+precision), y(1n+precision))

def Real.sum_is(+a: Q.Rational, +b: Q.Rational, -c: Q.Rational, -d: Q.Rational,
  a_is: {a == c : Q.Rational}, b_is: {b == d : Q.Rational}) ->
  {Q.Rational.add(a, b) == Q.Rational.add(c, d) : Q.Rational}:
  %a_is : {Q.Rational.add(a, b) == Q.Rational.add(_, d) : Q.Rational}
  %b_is : {Q.Rational.add(a, b) == Q.Rational.add(a, _) : Q.Rational}
  {==}

def Real.add_sample(-x: Nat -> Q.Rational, -y: Nat -> Q.Rational, +left_precision: Nat, +right_precision: Nat,
  x_sample: Real.Sample<x, 1n+left_precision, 1n+right_precision>,
  y_sample: Real.Sample<y, 1n+left_precision, 1n+right_precision>) ->
  Real.Sample<Real.add_approximations(x, y), left_precision, right_precision>:
  match x_sample y_sample:
    case Sample{+a, +b, a_is, b_is, x_close} Sample{+c, +d, c_is, d_is, y_close}:
      Sample{Q.Rational.add(a, c), Q.Rational.add(b, d),
        Real.sum_is(a, c, x(1n+left_precision), y(1n+left_precision), a_is, c_is),
        Real.sum_is(b, d, x(1n+right_precision), y(1n+right_precision), b_is, d_is),
        Q.Rational.close_halve_errors(Q.Rational.add(a, c), Q.Rational.add(b, d), left_precision, right_precision,
          Q.Rational.close_add_same_errors(a, b, c, d,
            Q.Rational.dyadic(1n+left_precision), Q.Rational.dyadic(1n+right_precision), x_close, y_close))}

def Real.add(x: Real, y: Real) -> Real:
  match x y:
    case Cauchy{x_approximate, x_regular} Cauchy{y_approximate, y_regular}:
      Cauchy{
        Real.add_approximations(x_approximate, y_approximate),
        +left_precision => +right_precision =>
          Real.add_sample(x_approximate, y_approximate, left_precision, right_precision,
            x_regular(1n+left_precision)(1n+right_precision),
            y_regular(1n+left_precision)(1n+right_precision))
      }
