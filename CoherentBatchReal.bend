import Base
import ./Rational.bend as Q
import ./Real.bend as R
import ./BatchReal.bend as B

type CertifiedPair<-canonical: Nat -> Q.Rational, -n: Nat, -m: Nat> is Type:
  Pair{
    left: Q.Rational,
    right: Q.Rational,
    left_identity: {left == canonical(n) : Q.Rational},
    right_identity: {right == canonical(m) : Q.Rational},
    close: Q.Rational.Close(left, right, Q.Rational.dyadic(n), Q.Rational.dyadic(m))
  }

type CoherentBatchReal is Type:
  Cauchy{
    -canonical: Nat -> Q.Rational,
    query: @n: Nat -> @m: Nat -> CertifiedPair<canonical, n, m>
  }

def CoherentBatchReal.Regular(x: CoherentBatchReal) -> Type:
  match x:
    case Cauchy{canonical, query}:
      @n: Nat -> @m: Nat ->
        Q.Rational.Close(canonical(n), canonical(m), Q.Rational.dyadic(n), Q.Rational.dyadic(m))

def CoherentBatchReal.Eq(x: CoherentBatchReal, y: CoherentBatchReal) -> Type:
  match x y:
    case Cauchy{left_canonical, left_query} Cauchy{right_canonical, right_query}:
      @n: Nat -> @m: Nat ->
        Q.Rational.Close(left_canonical(n), right_canonical(m), Q.Rational.dyadic(n), Q.Rational.dyadic(m))

def CoherentBatchReal.sample_regular(-canonical: Nat -> Q.Rational, +n: Nat, +m: Nat,
  sample: CertifiedPair<canonical, n, m>) ->
  Q.Rational.Close(canonical(n), canonical(m), Q.Rational.dyadic(n), Q.Rational.dyadic(m)):
  match sample:
    case Pair{left, right, left_identity, right_identity, close}:
      %left_identity : Q.Rational.Close(_, canonical(m), Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      %right_identity : Q.Rational.Close(left, _, Q.Rational.dyadic(n), Q.Rational.dyadic(m))
      close

def CoherentBatchReal.regular(x: CoherentBatchReal) -> CoherentBatchReal.Regular(x):
  match x:
    case Cauchy{canonical, query}:
      +n => +m => CoherentBatchReal.sample_regular(canonical, n, m, query(n)(m))

def CoherentBatchReal.eq_reflexive(x: CoherentBatchReal) -> CoherentBatchReal.Eq(x, x):
  match x:
    case Cauchy{canonical, query}:
      +n => +m => CoherentBatchReal.sample_regular(canonical, n, m, query(n)(m))

def CoherentBatchReal.close_symmetric(-x: Q.Rational, -y: Q.Rational,
  -left_error: Q.Rational, -right_error: Q.Rational,
  proof: Q.Rational.Close(x, y, left_error, right_error)) ->
  Q.Rational.Close(y, x, right_error, left_error):
  (forward, backward) = proof
  (backward, forward)

def CoherentBatchReal.close_rewrite(-a: Q.Rational, -b: Q.Rational,
  -c: Q.Rational, -d: Q.Rational, -left_error: Q.Rational, -right_error: Q.Rational,
  left_identity: {a == c : Q.Rational}, right_identity: {b == d : Q.Rational},
  proof: Q.Rational.Close(a, b, left_error, right_error)) ->
  Q.Rational.Close(c, d, left_error, right_error):
  %left_identity : Q.Rational.Close(_, d, left_error, right_error)
  %right_identity : Q.Rational.Close(a, _, left_error, right_error)
  proof

def CoherentBatchReal.eq_symmetric(x: CoherentBatchReal, y: CoherentBatchReal,
  proof: CoherentBatchReal.Eq(x, y)) -> CoherentBatchReal.Eq(y, x):
  match x y:
    case Cauchy{left_canonical, left_query} Cauchy{right_canonical, right_query}:
      +m => +n =>
        CoherentBatchReal.close_symmetric(
          left_canonical(n), right_canonical(m),
          Q.Rational.dyadic(n), Q.Rational.dyadic(m),
          proof(n)(m))

def CoherentBatchReal.add_equal(-a: Q.Rational, -b: Q.Rational, -c: Q.Rational, -d: Q.Rational,
  first: {a == b : Q.Rational}, second: {c == d : Q.Rational}) ->
  {Q.Rational.add(a, c) == Q.Rational.add(b, d) : Q.Rational}:
  Equal.trans(Q.Rational,
    Q.Rational.add(a, c), Q.Rational.add(b, c), Q.Rational.add(b, d),
    Equal.cong(Q.Rational, Q.Rational, z => Q.Rational.add(z, c), a, b, first),
    Equal.cong(Q.Rational, Q.Rational, z => Q.Rational.add(b, z), c, d, second))

def CoherentBatchReal.add_samples(-left_canonical: Nat -> Q.Rational, -right_canonical: Nat -> Q.Rational,
  +n: Nat, +m: Nat,
  first: CertifiedPair<left_canonical, 1n+n, 1n+m>,
  second: CertifiedPair<right_canonical, 1n+n, 1n+m>) ->
  CertifiedPair<(precision => Q.Rational.add(left_canonical(1n+precision), right_canonical(1n+precision))), n, m>:
  match first second:
    case Pair{+a, +b, a_identity, b_identity, first_close} Pair{+c, +d, c_identity, d_identity, second_close}:
      Pair{
        Q.Rational.add(a, c),
        Q.Rational.add(b, d),
        CoherentBatchReal.add_equal(
          a, left_canonical(1n+n), c, right_canonical(1n+n), a_identity, c_identity),
        CoherentBatchReal.add_equal(
          b, left_canonical(1n+m), d, right_canonical(1n+m), b_identity, d_identity),
        Q.Rational.close_halve_errors(
          Q.Rational.add(a, c), Q.Rational.add(b, d), n, m,
          Q.Rational.close_add_same_errors(
            a, b, c, d,
            Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m),
            first_close, second_close))
      }

def CoherentBatchReal.add(x: CoherentBatchReal, y: CoherentBatchReal) -> CoherentBatchReal:
  match x y:
    case Cauchy{left_canonical, left_query} Cauchy{right_canonical, right_query}:
      Cauchy{
        precision => Q.Rational.add(left_canonical(1n+precision), right_canonical(1n+precision)),
        +n => +m =>
          CoherentBatchReal.add_samples(left_canonical, right_canonical, n, m,
            left_query(1n+n)(1n+m),
            right_query(1n+n)(1n+m))
      }

def CoherentBatchReal.constant_sample(+value: Q.Rational, +n: Nat, +m: Nat) ->
  CertifiedPair<(precision => value), n, m>:
  Pair{
    value,
    value,
    {==},
    {==},
    R.Real.of_rational_close_from_bounds(value, value, n, m,
      Q.Rational.eq_both_le(value, value, Q.Rational.eq_reflexive(value)))
  }

def CoherentBatchReal.of_rational(+value: Q.Rational) -> CoherentBatchReal:
  Cauchy{
    precision => value,
    +n => +m => CoherentBatchReal.constant_sample(value, n, m)
  }

def CoherentBatchReal.add_eq_at(
  -left_canonical: Nat -> Q.Rational,
  -left_replacement_canonical: Nat -> Q.Rational,
  -right_canonical: Nat -> Q.Rational,
  -right_replacement_canonical: Nat -> Q.Rational,
  +n: Nat, +m: Nat,
  left_sample: CertifiedPair<left_canonical, 1n+n, 1n+n>,
  left_replacement_sample: CertifiedPair<left_replacement_canonical, 1n+m, 1n+m>,
  right_sample: CertifiedPair<right_canonical, 1n+n, 1n+n>,
  right_replacement_sample: CertifiedPair<right_replacement_canonical, 1n+m, 1n+m>,
  left_equality: Q.Rational.Close(
    left_canonical(1n+n), left_replacement_canonical(1n+m),
    Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m)),
  right_equality: Q.Rational.Close(
    right_canonical(1n+n), right_replacement_canonical(1n+m),
    Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m))) ->
  Q.Rational.Close(
    Q.Rational.add(left_canonical(1n+n), right_canonical(1n+n)),
    Q.Rational.add(left_replacement_canonical(1n+m), right_replacement_canonical(1n+m)),
    Q.Rational.dyadic(n), Q.Rational.dyadic(m)):
  match left_sample left_replacement_sample right_sample right_replacement_sample:
    case Pair{+a, discarded_left, +a_identity, discarded_left_identity, discarded_left_close}
         Pair{+b, discarded_left_replacement, +b_identity, discarded_left_replacement_identity, discarded_left_replacement_close}
         Pair{+c, discarded_right, +c_identity, discarded_right_identity, discarded_right_close}
         Pair{+d, discarded_right_replacement, +d_identity, discarded_right_replacement_identity, discarded_right_replacement_close}:
      CoherentBatchReal.close_rewrite(
        Q.Rational.add(a, c), Q.Rational.add(b, d),
        Q.Rational.add(left_canonical(1n+n), right_canonical(1n+n)),
        Q.Rational.add(left_replacement_canonical(1n+m), right_replacement_canonical(1n+m)),
        Q.Rational.dyadic(n), Q.Rational.dyadic(m),
        CoherentBatchReal.add_equal(
          a, left_canonical(1n+n), c, right_canonical(1n+n), a_identity, c_identity),
        CoherentBatchReal.add_equal(
          b, left_replacement_canonical(1n+m), d, right_replacement_canonical(1n+m),
          b_identity, d_identity),
        Q.Rational.close_halve_errors(
          Q.Rational.add(a, c), Q.Rational.add(b, d), n, m,
          Q.Rational.close_add_same_errors(
            a, b, c, d,
            Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m),
            CoherentBatchReal.close_rewrite(
              left_canonical(1n+n), left_replacement_canonical(1n+m), a, b,
              Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m),
              Equal.sym(Q.Rational, a, left_canonical(1n+n), a_identity),
              Equal.sym(Q.Rational, b, left_replacement_canonical(1n+m), b_identity),
              left_equality),
            CoherentBatchReal.close_rewrite(
              right_canonical(1n+n), right_replacement_canonical(1n+m), c, d,
              Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m),
              Equal.sym(Q.Rational, c, right_canonical(1n+n), c_identity),
              Equal.sym(Q.Rational, d, right_replacement_canonical(1n+m), d_identity),
              right_equality))))

def CoherentBatchReal.add_respects_eq(
  x: CoherentBatchReal, x_replacement: CoherentBatchReal,
  y: CoherentBatchReal, y_replacement: CoherentBatchReal,
  x_equality: CoherentBatchReal.Eq(x, x_replacement),
  y_equality: CoherentBatchReal.Eq(y, y_replacement)) ->
  CoherentBatchReal.Eq(
    CoherentBatchReal.add(x, y), CoherentBatchReal.add(x_replacement, y_replacement)):
  match x x_replacement y y_replacement:
    case Cauchy{left_canonical, left_query}
         Cauchy{left_replacement_canonical, left_replacement_query}
         Cauchy{right_canonical, right_query}
         Cauchy{right_replacement_canonical, right_replacement_query}:
      +n => +m =>
        CoherentBatchReal.add_eq_at(
          left_canonical, left_replacement_canonical,
          right_canonical, right_replacement_canonical, n, m,
          left_query(1n+n)(1n+n),
          left_replacement_query(1n+m)(1n+m),
          right_query(1n+n)(1n+n),
          right_replacement_query(1n+m)(1n+m),
          x_equality(1n+n)(1n+m),
          y_equality(1n+n)(1n+m))

def CoherentBatchReal.bad_impossible(
  query: @n: Nat -> @m: Nat -> CertifiedPair<B.BatchReal.bad_value, n, m>) -> Empty:
  B.BatchReal.bad_not_regular(
    CoherentBatchReal.sample_regular(B.BatchReal.bad_value, 0n, 1n+0n, query(0n)(1n+0n)))
