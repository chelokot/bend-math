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

def Real.add_respects_eq(x: Real, y: Real, other_x: Real, other_y: Real,
  x_equal: Real.Eq(x, other_x), y_equal: Real.Eq(y, other_y)) ->
  Real.Eq(Real.add(x, y), Real.add(other_x, other_y)):
  match x y other_x other_y:
    case Cauchy{x_approximate, x_regular} Cauchy{y_approximate, y_regular} Cauchy{other_x_approximate, other_x_regular} Cauchy{other_y_approximate, other_y_regular}:
      +left_precision => +right_precision =>
        +a: Q.Rational = x_approximate(1n+left_precision)
        +b: Q.Rational = y_approximate(1n+left_precision)
        +c: Q.Rational = other_x_approximate(1n+right_precision)
        +d: Q.Rational = other_y_approximate(1n+right_precision)
        Q.Rational.close_halve_errors(Q.Rational.add(a, b), Q.Rational.add(c, d), left_precision, right_precision,
          Q.Rational.close_add_same_errors(a, c, b, d,
            Q.Rational.dyadic(1n+left_precision), Q.Rational.dyadic(1n+right_precision),
            x_equal(1n+left_precision)(1n+right_precision), y_equal(1n+left_precision)(1n+right_precision)))

def Real.add_commutative_close(-x: Nat -> Q.Rational, -y: Nat -> Q.Rational, +left_precision: Nat, +right_precision: Nat,
  x_sample: Real.Sample<x, 1n+left_precision, 1n+right_precision>,
  y_sample: Real.Sample<y, 1n+left_precision, 1n+right_precision>) ->
  Q.Rational.Close(
    Q.Rational.add(x(1n+left_precision), y(1n+left_precision)),
    Q.Rational.add(y(1n+right_precision), x(1n+right_precision)),
    Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)):
  match x_sample y_sample:
    case Sample{+a, +b, a_is, b_is, x_close} Sample{+c, +d, c_is, d_is, y_close}:
      +swap: {Q.Rational.add(b, d) == Q.Rational.add(d, b) : Q.Rational} = Q.Rational.add_commutative(b, d)
      %a_is : Q.Rational.Close(Q.Rational.add(_, y(1n+left_precision)), Q.Rational.add(y(1n+right_precision), x(1n+right_precision)), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %c_is : Q.Rational.Close(Q.Rational.add(a, _), Q.Rational.add(y(1n+right_precision), x(1n+right_precision)), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %d_is : Q.Rational.Close(Q.Rational.add(a, c), Q.Rational.add(_, x(1n+right_precision)), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %b_is : Q.Rational.Close(Q.Rational.add(a, c), Q.Rational.add(d, _), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %swap : Q.Rational.Close(Q.Rational.add(a, c), _, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      Q.Rational.close_halve_errors(Q.Rational.add(a, c), Q.Rational.add(b, d), left_precision, right_precision,
        Q.Rational.close_add_same_errors(a, b, c, d,
          Q.Rational.dyadic(1n+left_precision), Q.Rational.dyadic(1n+right_precision), x_close, y_close))

def Real.add_commutative(x: Real, y: Real) -> Real.Eq(Real.add(x, y), Real.add(y, x)):
  match x y:
    case Cauchy{x_approximate, x_regular} Cauchy{y_approximate, y_regular}:
      +left_precision => +right_precision =>
        Real.add_commutative_close(x_approximate, y_approximate, left_precision, right_precision,
          x_regular(1n+left_precision)(1n+right_precision), y_regular(1n+left_precision)(1n+right_precision))

def Real.add_zero_close(-x: Nat -> Q.Rational, +left_precision: Nat, +right_precision: Nat,
  sample: Real.Sample<x, 1n+left_precision, right_precision>) ->
  Q.Rational.Close(Q.Rational.add(x(1n+left_precision), Q.Rational.zero()), x(right_precision),
    Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)):
  match sample:
    case Sample{+a, +b, a_is, b_is, close}:
      +unit: {a == Q.Rational.add(a, Q.Rational.zero()) : Q.Rational} =
        Equal.sym(Q.Rational, Q.Rational.add(a, Q.Rational.zero()), a, Q.Rational.add_zero(a))
      %a_is : Q.Rational.Close(Q.Rational.add(_, Q.Rational.zero()), x(right_precision), Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %b_is : Q.Rational.Close(Q.Rational.add(a, Q.Rational.zero()), _, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      %unit : Q.Rational.Close(_, b, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision))
      Q.Rational.close_weaken(a, b,
        Q.Rational.dyadic(1n+left_precision), Q.Rational.dyadic(right_precision),
        Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision),
        close, Q.Rational.dyadic_decreasing(left_precision), Q.Rational.le_reflexive(Q.Rational.dyadic(right_precision)))

def Real.add_zero(x: Real) -> Real.Eq(Real.add(x, Real.zero()), x):
  match x:
    case Cauchy{approximate, regular}:
      +left_precision => +right_precision =>
        Real.add_zero_close(approximate, left_precision, right_precision, regular(1n+left_precision)(right_precision))

def Real.neg_approximations(approximate: Nat -> Q.Rational) -> Nat -> Q.Rational:
  +precision => Q.Rational.neg(approximate(precision))

def Real.neg_sample(-approximate: Nat -> Q.Rational, +left_precision: Nat, +right_precision: Nat,
  sample: Real.Sample<approximate, left_precision, right_precision>) ->
  Real.Sample<Real.neg_approximations(approximate), left_precision, right_precision>:
  match sample:
    case Sample{+left, +right, left_is, right_is, close}:
      Sample{Q.Rational.neg(left), Q.Rational.neg(right),
        Equal.cong(Q.Rational, Q.Rational, z => Q.Rational.neg(z), left, approximate(left_precision), left_is),
        Equal.cong(Q.Rational, Q.Rational, z => Q.Rational.neg(z), right, approximate(right_precision), right_is),
        Q.Rational.close_negated(left, right, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision), close)}

def Real.neg(x: Real) -> Real:
  match x:
    case Cauchy{approximate, regular}:
      Cauchy{
        Real.neg_approximations(approximate),
        +left_precision => +right_precision =>
          Real.neg_sample(approximate, left_precision, right_precision, regular(left_precision)(right_precision))
      }

def Real.neg_respects_eq(x: Real, y: Real, equal: Real.Eq(x, y)) -> Real.Eq(Real.neg(x), Real.neg(y)):
  match x y:
    case Cauchy{x_approximate, x_regular} Cauchy{y_approximate, y_regular}:
      +left_precision => +right_precision =>
        +a: Q.Rational = x_approximate(left_precision)
        +b: Q.Rational = y_approximate(right_precision)
        Q.Rational.close_negated(a, b, Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision),
          equal(left_precision)(right_precision))

def Real.add_neg(x: Real) -> Real.Eq(Real.add(x, Real.neg(x)), Real.zero()):
  match x:
    case Cauchy{approximate, regular}:
      +left_precision => +right_precision =>
        +a: Q.Rational = approximate(1n+left_precision)
        Q.Rational.close_of_eq_dyadic(Q.Rational.add(a, Q.Rational.neg(a)), Q.Rational.zero(),
          left_precision, right_precision, Q.Rational.add_neg_self(a))

def Real.add_associative_close(-x: Nat -> Q.Rational, -y: Nat -> Q.Rational, -z: Nat -> Q.Rational,
  +left_precision: Nat, +right_precision: Nat,
  x_sample: Real.Sample<x, 2n+left_precision, 1n+right_precision>,
  y_sample: Real.Sample<y, 2n+left_precision, 2n+right_precision>,
  z_sample: Real.Sample<z, 1n+left_precision, 2n+right_precision>) ->
  Q.Rational.Close(
    Q.Rational.add(Q.Rational.add(x(2n+left_precision), y(2n+left_precision)), z(1n+left_precision)),
    Q.Rational.add(x(1n+right_precision), Q.Rational.add(y(2n+right_precision), z(2n+right_precision))),
    Q.Rational.dyadic(left_precision), Q.Rational.dyadic(right_precision)):
  match x_sample y_sample z_sample:
    case Sample{+a, +b, a_is, b_is, x_close} Sample{+c, +d, c_is, d_is, y_close} Sample{+e, +f, e_is, f_is, z_close}:
      +n: Nat = left_precision
      +m: Nat = right_precision
      +left_errors: Q.Rational = Q.Rational.add(Q.Rational.add(Q.Rational.dyadic(2n+n), Q.Rational.dyadic(2n+n)), Q.Rational.dyadic(1n+n))
      +right_errors: Q.Rational = Q.Rational.add(Q.Rational.add(Q.Rational.dyadic(1n+m), Q.Rational.dyadic(2n+m)), Q.Rational.dyadic(2n+m))
      +regroup: {Q.Rational.add(Q.Rational.add(b, d), f) == Q.Rational.add(b, Q.Rational.add(d, f)) : Q.Rational} =
        Q.Rational.add_associative(b, d, f)
      %a_is : Q.Rational.Close(Q.Rational.add(Q.Rational.add(_, y(2n+n)), z(1n+n)), Q.Rational.add(x(1n+m), Q.Rational.add(y(2n+m), z(2n+m))), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %c_is : Q.Rational.Close(Q.Rational.add(Q.Rational.add(a, _), z(1n+n)), Q.Rational.add(x(1n+m), Q.Rational.add(y(2n+m), z(2n+m))), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %e_is : Q.Rational.Close(Q.Rational.add(Q.Rational.add(a, c), _), Q.Rational.add(x(1n+m), Q.Rational.add(y(2n+m), z(2n+m))), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %b_is : Q.Rational.Close(Q.Rational.add(Q.Rational.add(a, c), e), Q.Rational.add(_, Q.Rational.add(y(2n+m), z(2n+m))), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %d_is : Q.Rational.Close(Q.Rational.add(Q.Rational.add(a, c), e), Q.Rational.add(b, Q.Rational.add(_, z(2n+m))), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %f_is : Q.Rational.Close(Q.Rational.add(Q.Rational.add(a, c), e), Q.Rational.add(b, Q.Rational.add(d, _)), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %regroup : Q.Rational.Close(Q.Rational.add(Q.Rational.add(a, c), e), _, Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      Q.Rational.close_replace_errors(
        Q.Rational.add(Q.Rational.add(a, c), e), Q.Rational.add(Q.Rational.add(b, d), f),
        left_errors, right_errors, Q.Rational.dyadic(n), Q.Rational.dyadic(m),
        Q.Rational.close_add(Q.Rational.add(a, c), Q.Rational.add(b, d), e, f,
          Q.Rational.add(Q.Rational.dyadic(2n+n), Q.Rational.dyadic(2n+n)), Q.Rational.add(Q.Rational.dyadic(1n+m), Q.Rational.dyadic(2n+m)),
          Q.Rational.dyadic(1n+n), Q.Rational.dyadic(2n+m),
          Q.Rational.close_add(a, b, c, d,
            Q.Rational.dyadic(2n+n), Q.Rational.dyadic(1n+m), Q.Rational.dyadic(2n+n), Q.Rational.dyadic(2n+m),
            x_close, y_close),
          z_close),
        Q.Rational.eq_add_both(left_errors, Q.Rational.dyadic(n), right_errors, Q.Rational.dyadic(m),
          Q.Rational.dyadic_three_left(n), Q.Rational.dyadic_three_right(m)),
        Q.Rational.eq_add_both(right_errors, Q.Rational.dyadic(m), left_errors, Q.Rational.dyadic(n),
          Q.Rational.dyadic_three_right(m), Q.Rational.dyadic_three_left(n)))

def Real.add_associative(x: Real, y: Real, z: Real) ->
  Real.Eq(Real.add(Real.add(x, y), z), Real.add(x, Real.add(y, z))):
  match x y z:
    case Cauchy{x_approximate, x_regular} Cauchy{y_approximate, y_regular} Cauchy{z_approximate, z_regular}:
      +left_precision => +right_precision =>
        Real.add_associative_close(x_approximate, y_approximate, z_approximate, left_precision, right_precision,
          x_regular(2n+left_precision)(1n+right_precision),
          y_regular(2n+left_precision)(2n+right_precision),
          z_regular(1n+left_precision)(2n+right_precision))
