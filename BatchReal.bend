import Base
import ./Rational.bend as Q
import ./Real.bend as R

type PairSample<-n: Nat, -m: Nat> is Type:
  Pair{
    left: Q.Rational,
    right: Q.Rational,
    close: Q.Rational.Close(left, right, Q.Rational.dyadic(n), Q.Rational.dyadic(m))
  }

type BatchReal is Type:
  Cauchy{query: @n: Nat -> @m: Nat -> PairSample<n, m>}

def BatchReal.add_samples(+n: Nat, +m: Nat,
  first: PairSample<1n+n, 1n+m>,
  second: PairSample<1n+n, 1n+m>) -> PairSample<n, m>:
  match first second:
    case Pair{+a, +b, first_close} Pair{+c, +d, second_close}:
      Pair{
        Q.Rational.add(a, c),
        Q.Rational.add(b, d),
        Q.Rational.close_halve_errors(
          Q.Rational.add(a, c), Q.Rational.add(b, d), n, m,
          Q.Rational.close_add_same_errors(
            a, b, c, d,
            Q.Rational.dyadic(1n+n), Q.Rational.dyadic(1n+m),
            first_close, second_close))
      }

def BatchReal.add(x: BatchReal, y: BatchReal) -> BatchReal:
  match x y:
    case Cauchy{left_query} Cauchy{right_query}:
      Cauchy{
        +n => +m =>
          BatchReal.add_samples(n, m,
            left_query(1n+n)(1n+m),
            right_query(1n+n)(1n+m))
      }

def BatchReal.constant_sample(+value: Q.Rational, +n: Nat, +m: Nat) -> PairSample<n, m>:
  Pair{
    value,
    value,
    R.Real.of_rational_close_from_bounds(value, value, n, m,
      Q.Rational.eq_both_le(value, value, Q.Rational.eq_reflexive(value)))
  }

def BatchReal.of_rational(+value: Q.Rational) -> BatchReal:
  Cauchy{+n => +m => BatchReal.constant_sample(value, n, m)}

def BatchReal.bad_value(n: Nat) -> Q.Rational:
  match n:
    case 0n:
      Q.Rational.zero()
    case 1n+predecessor:
      Q.Rational.of_nat(3n)

def BatchReal.bad() -> BatchReal:
  Cauchy{+n => +m => BatchReal.constant_sample(BatchReal.bad_value(n), n, m)}

def BatchReal.sample_left(-n: Nat, sample: PairSample<n, n>) -> Q.Rational:
  match sample:
    case Pair{left, right, close}:
      left

def BatchReal.diagonal(x: BatchReal, +n: Nat) -> Q.Rational:
  match x:
    case Cauchy{query}:
      BatchReal.sample_left(n, query(n)(n))

def BatchReal.bad_not_regular(
  proof: Q.Rational.Close(
    BatchReal.diagonal(BatchReal.bad(), 0n),
    BatchReal.diagonal(BatchReal.bad(), 1n+0n),
    Q.Rational.dyadic(0n), Q.Rational.dyadic(1n+0n))) -> Empty:
  (forward, backward) = proof
  backward
