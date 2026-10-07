import Base
import ./Field.bend as K
import ./FieldAlgebra.bend as A
import ./FieldRing.bend as R
import ./FieldOrder.bend as O
import ./Certificate.bend as C
import ./Natural.bend as N

type Intervals.Interval<-F: Kind(&2)> is Data:
  Interval{lo: F, hi: F}

def Intervals.lo(-F: Kind(&2), interval: Intervals.Interval<F>) -> F:
  match interval:
    case Interval{lo, hi}:
      lo

def Intervals.hi(-F: Kind(&2), interval: Intervals.Interval<F>) -> F:
  match interval:
    case Interval{lo, hi}:
      hi

def Intervals.minus(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> F:
  A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b))

def Intervals.length(~F: Kind(&2), ~field: K.Field<F>, +interval: Intervals.Interval<F>) -> F:
  Intervals.minus(~F, ~field, Intervals.hi(F, interval), Intervals.lo(F, interval))

def Intervals.count(-F: Kind(&2), list: List<&2, Intervals.Interval<F>>) -> Nat:
  match list:
    case Nil{}:
      0n
    case interval <> rest:
      1n+Intervals.count(F, rest)

def Intervals.total(~F: Kind(&2), ~field: K.Field<F>, list: List<&2, Intervals.Interval<F>>) -> F:
  match list:
    case Nil{}:
      A.Algebra.zero(~F, ~field)
    case +interval <> rest:
      A.Algebra.add(~F, ~field, Intervals.length(~F, ~field, interval), Intervals.total(~F, ~field, rest))

def Intervals.Inside(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +interval: Intervals.Interval<F>) -> Kind(&2):
  C.Certificate.Both<A.Algebra.le(~F, ~field, a, Intervals.lo(F, interval)),
    C.Certificate.Both<A.Algebra.le(~F, ~field, Intervals.lo(F, interval), Intervals.hi(F, interval)), A.Algebra.le(~F, ~field, Intervals.hi(F, interval), b)>>

def Intervals.Within(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, list: List<&2, Intervals.Interval<F>>) -> Kind(&2):
  match list:
    case Nil{}:
      Unit
    case +interval <> rest:
      C.Certificate.Both<Intervals.Inside(~F, ~field, a, b, interval), Intervals.Within(~F, ~field, a, b, rest)>

def Intervals.Apart(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, +second: Intervals.Interval<F>) -> Kind(&2):
  Either<&2, &2, A.Algebra.le(~F, ~field, Intervals.hi(F, first), Intervals.lo(F, second)), A.Algebra.le(~F, ~field, Intervals.hi(F, second), Intervals.lo(F, first))>

def Intervals.ApartAll(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, list: List<&2, Intervals.Interval<F>>) -> Kind(&2):
  match list:
    case Nil{}:
      Unit
    case +interval <> rest:
      C.Certificate.Both<Intervals.Apart(~F, ~field, first, interval), Intervals.ApartAll(~F, ~field, first, rest)>

def Intervals.Pairwise(~F: Kind(&2), ~field: K.Field<F>, list: List<&2, Intervals.Interval<F>>) -> Kind(&2):
  match list:
    case Nil{}:
      Unit
    case +interval <> rest:
      C.Certificate.Both<Intervals.ApartAll(~F, ~field, interval, rest), Intervals.Pairwise(~F, ~field, rest)>

def Intervals.shift_one(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, +interval: Intervals.Interval<F>,
  side: Intervals.Apart(~F, ~field, first, interval)) -> Intervals.Interval<F>:
  match side:
    case Inl{right}:
      Interval{Intervals.minus(~F, ~field, Intervals.lo(F, interval), Intervals.length(~F, ~field, first)),
        Intervals.minus(~F, ~field, Intervals.hi(F, interval), Intervals.length(~F, ~field, first))}
    case Inr{left}:
      interval

def Intervals.shift(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, list: List<&2, Intervals.Interval<F>>,
  apart: Intervals.ApartAll(~F, ~field, first, list)) -> List<&2, Intervals.Interval<F>>:
  match list:
    case Nil{}:
      Nil{}
    case +interval <> rest:
      match apart:
        case C.Both{side, others}:
          Intervals.shift_one(~F, ~field, first, interval, side) <> Intervals.shift(~F, ~field, first, rest, others)

def Intervals.count_shift(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, list: List<&2, Intervals.Interval<F>>,
  apart: Intervals.ApartAll(~F, ~field, first, list)) -> {Intervals.count(F, Intervals.shift(~F, ~field, first, list, apart)) == Intervals.count(F, list) : Nat}:
  match list:
    case Nil{}:
      {==}
    case +interval <> rest:
      match apart:
        case C.Both{side, others}:
          Equal.cong(Nat, Nat, z => 1n+z, Intervals.count(F, Intervals.shift(~F, ~field, first, rest, others)), Intervals.count(F, rest),
            Intervals.count_shift(~F, ~field, first, rest, others))

def Intervals.le_trans(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, ab: A.Algebra.le(~F, ~field, a, b), bc: A.Algebra.le(~F, ~field, b, c)) ->
  A.Algebra.le(~F, ~field, a, c):
  K.Field.le_transitive(F, field)(a, b, c, ab, bc)

def Intervals.le_shift(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, +d: F, xy: A.Algebra.le(~F, ~field, x, y)) ->
  A.Algebra.le(~F, ~field, Intervals.minus(~F, ~field, x, d), Intervals.minus(~F, ~field, y, d)):
  K.Field.le_add(F, field)(x, y, A.Algebra.neg(~F, ~field, d), xy)

def Intervals.shifted_length(~F: Kind(&2), ~field: K.Field<F>, +lo: F, +hi: F, +d: F) ->
  A.Algebra.Same(~F, ~field, Intervals.minus(~F, ~field, Intervals.minus(~F, ~field, hi, d), Intervals.minus(~F, ~field, lo, d)), Intervals.minus(~F, ~field, hi, lo)):
  R.FieldRing.equal(~F, ~field, R.Value{hi, R.Value{lo, R.Value{d, R.NoValues{}}}},
    R.Plus{R.Plus{R.Variable{0n}, R.Negate{R.Variable{2n}}}, R.Negate{R.Plus{R.Variable{1n}, R.Negate{R.Variable{2n}}}}},
    R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, {==})

def Intervals.back(~F: Kind(&2), ~field: K.Field<F>, +lo: F, +hi: F) ->
  A.Algebra.Same(~F, ~field, Intervals.minus(~F, ~field, hi, Intervals.minus(~F, ~field, hi, lo)), lo):
  R.FieldRing.equal(~F, ~field, R.Value{hi, R.Value{lo, R.NoValues{}}},
    R.Plus{R.Variable{0n}, R.Negate{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}}}, R.Variable{1n}, {==})

def Intervals.recombine(~F: Kind(&2), ~field: K.Field<F>, +d: F, +a: F, +b: F) ->
  A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, d, Intervals.minus(~F, ~field, Intervals.minus(~F, ~field, b, d), a)), Intervals.minus(~F, ~field, b, a)):
  R.FieldRing.equal(~F, ~field, R.Value{d, R.Value{a, R.Value{b, R.NoValues{}}}},
    R.Plus{R.Variable{0n}, R.Plus{R.Plus{R.Variable{2n}, R.Negate{R.Variable{0n}}}, R.Negate{R.Variable{1n}}}},
    R.Plus{R.Variable{2n}, R.Negate{R.Variable{1n}}}, {==})

def Intervals.cancel(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> A.Algebra.Same(~F, ~field, Intervals.minus(~F, ~field, a, a), A.Algebra.zero(~F, ~field)):
  R.FieldRing.equal(~F, ~field, R.Value{a, R.NoValues{}}, R.Plus{R.Variable{0n}, R.Negate{R.Variable{0n}}}, R.Number{0n}, {==})

def Intervals.below_shifted(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, +x: F,
  right: A.Algebra.le(~F, ~field, Intervals.hi(F, first), x)) ->
  A.Algebra.le(~F, ~field, Intervals.lo(F, first), Intervals.minus(~F, ~field, x, Intervals.length(~F, ~field, first))):
  +d: F = Intervals.length(~F, ~field, first)
  A.Algebra.le_respects(~F, ~field, Intervals.minus(~F, ~field, Intervals.hi(F, first), d), Intervals.minus(~F, ~field, x, d),
    Intervals.lo(F, first), Intervals.minus(~F, ~field, x, d), Intervals.le_shift(~F, ~field, Intervals.hi(F, first), x, d, right),
    Intervals.back(~F, ~field, Intervals.lo(F, first), Intervals.hi(F, first)), A.Algebra.same_reflexive(~F, ~field, Intervals.minus(~F, ~field, x, d)))

def Intervals.length_one(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, +interval: Intervals.Interval<F>,
  side: Intervals.Apart(~F, ~field, first, interval)) ->
  A.Algebra.Same(~F, ~field, Intervals.length(~F, ~field, Intervals.shift_one(~F, ~field, first, interval, side)), Intervals.length(~F, ~field, interval)):
  match side:
    case Inl{right}:
      Intervals.shifted_length(~F, ~field, Intervals.lo(F, interval), Intervals.hi(F, interval), Intervals.length(~F, ~field, first))
    case Inr{left}:
      A.Algebra.same_reflexive(~F, ~field, Intervals.length(~F, ~field, interval))

def Intervals.total_shift(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, list: List<&2, Intervals.Interval<F>>,
  apart: Intervals.ApartAll(~F, ~field, first, list)) ->
  A.Algebra.Same(~F, ~field, Intervals.total(~F, ~field, Intervals.shift(~F, ~field, first, list, apart)), Intervals.total(~F, ~field, list)):
  match list:
    case Nil{}:
      A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field))
    case +interval <> +rest:
      match apart:
        case C.Both{+side, +others}:
          A.Algebra.add_respects(~F, ~field, Intervals.length(~F, ~field, Intervals.shift_one(~F, ~field, first, interval, side)), Intervals.length(~F, ~field, interval),
            Intervals.total(~F, ~field, Intervals.shift(~F, ~field, first, rest, others)), Intervals.total(~F, ~field, rest),
            Intervals.length_one(~F, ~field, first, interval, side), Intervals.total_shift(~F, ~field, first, rest, others))

def Intervals.inside_one(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +first: Intervals.Interval<F>, inside_first: Intervals.Inside(~F, ~field, a, b, first),
  +interval: Intervals.Interval<F>, inside: Intervals.Inside(~F, ~field, a, b, interval), side: Intervals.Apart(~F, ~field, first, interval)) ->
  Intervals.Inside(~F, ~field, a, Intervals.minus(~F, ~field, b, Intervals.length(~F, ~field, first)), Intervals.shift_one(~F, ~field, first, interval, side)):
  match inside_first:
    case C.Both{first_low, first_rest}:
      match first_rest:
        case C.Both{first_ordered, first_high}:
          match inside:
            case C.Both{low, rest}:
              match rest:
                case C.Both{ordered, high}:
                  match side:
                    case Inl{right}:
                      +d: F = Intervals.length(~F, ~field, first)
                      C.Both{Intervals.le_trans(~F, ~field, a, Intervals.lo(F, first), Intervals.minus(~F, ~field, Intervals.lo(F, interval), d), first_low,
                          Intervals.below_shifted(~F, ~field, first, Intervals.lo(F, interval), right)),
                        C.Both{Intervals.le_shift(~F, ~field, Intervals.lo(F, interval), Intervals.hi(F, interval), d, ordered),
                          Intervals.le_shift(~F, ~field, Intervals.hi(F, interval), b, d, high)}}
                    case Inr{left}:
                      +d: F = Intervals.length(~F, ~field, first)
                      C.Both{low, C.Both{ordered,
                        Intervals.le_trans(~F, ~field, Intervals.hi(F, interval), Intervals.lo(F, first), Intervals.minus(~F, ~field, b, d), left,
                          Intervals.below_shifted(~F, ~field, first, b, first_high))}}

def Intervals.within_shift(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +first: Intervals.Interval<F>, +inside_first: Intervals.Inside(~F, ~field, a, b, first),
  list: List<&2, Intervals.Interval<F>>, within: Intervals.Within(~F, ~field, a, b, list), apart: Intervals.ApartAll(~F, ~field, first, list)) ->
  Intervals.Within(~F, ~field, a, Intervals.minus(~F, ~field, b, Intervals.length(~F, ~field, first)), Intervals.shift(~F, ~field, first, list, apart)):
  match list:
    case Nil{}:
      Unit{}
    case +interval <> rest:
      match within:
        case C.Both{inside, within_rest}:
          match apart:
            case C.Both{+side, others}:
              C.Both{Intervals.inside_one(~F, ~field, a, b, first, inside_first, interval, inside, side),
                Intervals.within_shift(~F, ~field, a, b, first, inside_first, rest, within_rest, others)}

def Intervals.apart_pair(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, +one: Intervals.Interval<F>, side_one: Intervals.Apart(~F, ~field, first, one),
  +other: Intervals.Interval<F>, side_other: Intervals.Apart(~F, ~field, first, other), apart: Intervals.Apart(~F, ~field, one, other)) ->
  Intervals.Apart(~F, ~field, Intervals.shift_one(~F, ~field, first, one, side_one), Intervals.shift_one(~F, ~field, first, other, side_other)):
  match side_one:
    case Inl{one_right}:
      match side_other:
        case Inl{other_right}:
          match apart:
            case Inl{before}:
              Inl{Intervals.le_shift(~F, ~field, Intervals.hi(F, one), Intervals.lo(F, other), Intervals.length(~F, ~field, first), before)}
            case Inr{after}:
              Inr{Intervals.le_shift(~F, ~field, Intervals.hi(F, other), Intervals.lo(F, one), Intervals.length(~F, ~field, first), after)}
        case Inr{other_left}:
          Inr{Intervals.le_trans(~F, ~field, Intervals.hi(F, other), Intervals.lo(F, first),
            Intervals.minus(~F, ~field, Intervals.lo(F, one), Intervals.length(~F, ~field, first)), other_left,
            Intervals.below_shifted(~F, ~field, first, Intervals.lo(F, one), one_right))}
    case Inr{one_left}:
      match side_other:
        case Inl{other_right}:
          Inl{Intervals.le_trans(~F, ~field, Intervals.hi(F, one), Intervals.lo(F, first),
            Intervals.minus(~F, ~field, Intervals.lo(F, other), Intervals.length(~F, ~field, first)), one_left,
            Intervals.below_shifted(~F, ~field, first, Intervals.lo(F, other), other_right))}
        case Inr{other_left}:
          apart

def Intervals.apart_all_shift(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, +one: Intervals.Interval<F>, +side_one: Intervals.Apart(~F, ~field, first, one),
  list: List<&2, Intervals.Interval<F>>, others: Intervals.ApartAll(~F, ~field, first, list), apart: Intervals.ApartAll(~F, ~field, one, list)) ->
  Intervals.ApartAll(~F, ~field, Intervals.shift_one(~F, ~field, first, one, side_one), Intervals.shift(~F, ~field, first, list, others)):
  match list:
    case Nil{}:
      Unit{}
    case +other <> rest:
      match others:
        case C.Both{+side_other, others_rest}:
          match apart:
            case C.Both{pair, apart_rest}:
              C.Both{Intervals.apart_pair(~F, ~field, first, one, side_one, other, side_other, pair),
                Intervals.apart_all_shift(~F, ~field, first, one, side_one, rest, others_rest, apart_rest)}

def Intervals.pairwise_shift(~F: Kind(&2), ~field: K.Field<F>, +first: Intervals.Interval<F>, list: List<&2, Intervals.Interval<F>>,
  apart: Intervals.ApartAll(~F, ~field, first, list), pairwise: Intervals.Pairwise(~F, ~field, list)) ->
  Intervals.Pairwise(~F, ~field, Intervals.shift(~F, ~field, first, list, apart)):
  match list:
    case Nil{}:
      Unit{}
    case +interval <> +rest:
      match apart:
        case C.Both{+side, +others}:
          match pairwise:
            case C.Both{apart_interval, pairwise_rest}:
              C.Both{Intervals.apart_all_shift(~F, ~field, first, interval, side, rest, others, apart_interval),
                Intervals.pairwise_shift(~F, ~field, first, rest, others, pairwise_rest)}

def Intervals.empty_bound(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, order: A.Algebra.le(~F, ~field, a, b)) ->
  A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Intervals.minus(~F, ~field, b, a)):
  A.Algebra.le_respects(~F, ~field, Intervals.minus(~F, ~field, a, a), Intervals.minus(~F, ~field, b, a), A.Algebra.zero(~F, ~field), Intervals.minus(~F, ~field, b, a),
    Intervals.le_shift(~F, ~field, a, b, a, order), Intervals.cancel(~F, ~field, a), A.Algebra.same_reflexive(~F, ~field, Intervals.minus(~F, ~field, b, a)))

def Intervals.order_after(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +first: Intervals.Interval<F>, inside: Intervals.Inside(~F, ~field, a, b, first)) ->
  A.Algebra.le(~F, ~field, a, Intervals.minus(~F, ~field, b, Intervals.length(~F, ~field, first))):
  match inside:
    case C.Both{low, rest}:
      match rest:
        case C.Both{ordered, high}:
          Intervals.le_trans(~F, ~field, a, Intervals.lo(F, first), Intervals.minus(~F, ~field, b, Intervals.length(~F, ~field, first)), low,
            Intervals.below_shifted(~F, ~field, first, b, high))

def Intervals.total_bound(~F: Kind(&2), ~field: K.Field<F>, +fuel: Nat, +a: F, +b: F, list: List<&2, Intervals.Interval<F>>,
  short: N.Natural.Le(Intervals.count(F, list), fuel), order: A.Algebra.le(~F, ~field, a, b),
  within: Intervals.Within(~F, ~field, a, b, list), pairwise: Intervals.Pairwise(~F, ~field, list)) ->
  A.Algebra.le(~F, ~field, Intervals.total(~F, ~field, list), Intervals.minus(~F, ~field, b, a)):
  match fuel:
    case 0n:
      match list:
        case Nil{}:
          Intervals.empty_bound(~F, ~field, a, b, order)
        case interval <> rest:
          Empty.absurd(A.Algebra.le(~F, ~field, Intervals.total(~F, ~field, interval <> rest), Intervals.minus(~F, ~field, b, a)), short)
    case 1n+previous:
      match list:
        case Nil{}:
          Intervals.empty_bound(~F, ~field, a, b, order)
        case +first <> +rest:
          match within:
            case C.Both{+inside, within_rest}:
              match pairwise:
                case C.Both{+apart, pairwise_rest}:
                  +d: F = Intervals.length(~F, ~field, first)
                  +narrow: F = Intervals.minus(~F, ~field, b, d)
                  +shifted: List<&2, Intervals.Interval<F>> = Intervals.shift(~F, ~field, first, rest, apart)
                  +bound: A.Algebra.le(~F, ~field, Intervals.total(~F, ~field, shifted), Intervals.minus(~F, ~field, narrow, a)) =
                    Intervals.total_bound(~F, ~field, previous, a, narrow, shifted,
                      N.Natural.le_congruent(Intervals.count(F, rest), previous, Intervals.count(F, shifted), previous, short,
                        Equal.sym(Nat, Intervals.count(F, shifted), Intervals.count(F, rest), Intervals.count_shift(~F, ~field, first, rest, apart)), {==}),
                      Intervals.order_after(~F, ~field, a, b, first, inside),
                      Intervals.within_shift(~F, ~field, a, b, first, inside, rest, within_rest, apart),
                      Intervals.pairwise_shift(~F, ~field, first, rest, apart, pairwise_rest))
                  +rest_bound: A.Algebra.le(~F, ~field, Intervals.total(~F, ~field, rest), Intervals.minus(~F, ~field, narrow, a)) =
                    A.Algebra.le_respects(~F, ~field, Intervals.total(~F, ~field, shifted), Intervals.minus(~F, ~field, narrow, a),
                      Intervals.total(~F, ~field, rest), Intervals.minus(~F, ~field, narrow, a), bound,
                      Intervals.total_shift(~F, ~field, first, rest, apart), A.Algebra.same_reflexive(~F, ~field, Intervals.minus(~F, ~field, narrow, a)))
                  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, d, Intervals.total(~F, ~field, rest)), A.Algebra.add(~F, ~field, d, Intervals.minus(~F, ~field, narrow, a)),
                    A.Algebra.add(~F, ~field, d, Intervals.total(~F, ~field, rest)), Intervals.minus(~F, ~field, b, a),
                    O.FieldOrder.le_add_left(~F, ~field, Intervals.total(~F, ~field, rest), Intervals.minus(~F, ~field, narrow, a), d, rest_bound),
                    A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, d, Intervals.total(~F, ~field, rest))),
                    Intervals.recombine(~F, ~field, d, a, b))

def Intervals.packed(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +list: List<&2, Intervals.Interval<F>>, order: A.Algebra.le(~F, ~field, a, b),
  within: Intervals.Within(~F, ~field, a, b, list), pairwise: Intervals.Pairwise(~F, ~field, list)) ->
  A.Algebra.le(~F, ~field, Intervals.total(~F, ~field, list), Intervals.minus(~F, ~field, b, a)):
  Intervals.total_bound(~F, ~field, Intervals.count(F, list), a, b, list, N.Natural.le_reflexive(Intervals.count(F, list)), order, within, pairwise)
