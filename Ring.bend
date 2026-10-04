import Base
import ./Natural.bend as N

type Ring.Expr is Data:
  Atom{index: Nat}
  Constant{value: Nat}
  Next{body: Ring.Expr}
  Sum{left: Ring.Expr, right: Ring.Expr}
  Product{left: Ring.Expr, right: Ring.Expr}

type Ring.Values is Data:
  NoValues{}
  Value{head: Nat, tail: Ring.Values}

type Ring.Monomial is Data:
  One{}
  Times{index: Nat, rest: Ring.Monomial}

type Ring.Poly is Data:
  NoTerms{}
  Term{coefficient: Nat, monomial: Ring.Monomial, rest: Ring.Poly}

def Ring.lookup(values: Ring.Values, index: Nat) -> Nat:
  match values:
    case NoValues{}:
      0n
    case Value{head, tail}:
      match index:
        case 0n:
          head
        case 1n+previous:
          Ring.lookup(tail, previous)

def Ring.eval(+values: Ring.Values, expr: Ring.Expr) -> Nat:
  match expr:
    case Atom{index}:
      Ring.lookup(values, index)
    case Constant{value}:
      value
    case Next{body}:
      1n+Ring.eval(values, body)
    case Sum{left, right}:
      Nat.add(Ring.eval(values, left), Ring.eval(values, right))
    case Product{left, right}:
      Nat.mul(Ring.eval(values, left), Ring.eval(values, right))

def Ring.eval_monomial(+values: Ring.Values, monomial: Ring.Monomial) -> Nat:
  match monomial:
    case One{}:
      1n
    case Times{index, rest}:
      Nat.mul(Ring.lookup(values, index), Ring.eval_monomial(values, rest))

def Ring.eval_poly(+values: Ring.Values, poly: Ring.Poly) -> Nat:
  match poly:
    case NoTerms{}:
      0n
    case Term{coefficient, monomial, rest}:
      Nat.add(Nat.mul(coefficient, Ring.eval_monomial(values, monomial)), Ring.eval_poly(values, rest))

def Ring.then(first: Cmp, second: Cmp) -> Cmp:
  match first:
    case LT{}:
      LT{}
    case EQ{}:
      second
    case GT{}:
      GT{}

def Ring.compare(left: Ring.Monomial, right: Ring.Monomial) -> Cmp:
  match left right:
    case One{} One{}:
      EQ{}
    case One{} Times{index, rest}:
      LT{}
    case Times{index, rest} One{}:
      GT{}
    case Times{left_index, left_rest} Times{right_index, right_rest}:
      Ring.then(Nat.cmp(left_index, right_index), Ring.compare(left_rest, right_rest))

def Ring.choose_monomial(order: Cmp, less: Ring.Monomial, equal: Ring.Monomial, greater: Ring.Monomial) -> Ring.Monomial:
  match order:
    case LT{}:
      less
    case EQ{}:
      equal
    case GT{}:
      greater

def Ring.choose_poly(order: Cmp, less: Ring.Poly, equal: Ring.Poly, greater: Ring.Poly) -> Ring.Poly:
  match order:
    case LT{}:
      less
    case EQ{}:
      equal
    case GT{}:
      greater

def Ring.merge(+left: Ring.Monomial, +right: Ring.Monomial) -> Ring.Monomial:
  match left right:
    case One{} One{}:
      One{}
    case One{} Times{index, rest}:
      Times{index, rest}
    case Times{index, rest} One{}:
      Times{index, rest}
    case Times{+left_index, +left_rest} Times{+right_index, +right_rest}:
      Ring.choose_monomial(Nat.cmp(left_index, right_index),
        Times{left_index, Ring.merge(left_rest, Times{right_index, right_rest})},
        Times{left_index, Ring.merge(left_rest, Times{right_index, right_rest})},
        Times{right_index, Ring.merge(Times{left_index, left_rest}, right_rest)})

def Ring.insert(+coefficient: Nat, +monomial: Ring.Monomial, +poly: Ring.Poly) -> Ring.Poly:
  match coefficient:
    case 0n:
      poly
    case 1n+previous:
      match poly:
        case NoTerms{}:
          Term{coefficient, monomial, NoTerms{}}
        case Term{+other_coefficient, +other_monomial, +rest}:
          Ring.choose_poly(Ring.compare(monomial, other_monomial),
            Term{coefficient, monomial, Term{other_coefficient, other_monomial, rest}},
            Term{Nat.add(coefficient, other_coefficient), other_monomial, rest},
            Term{other_coefficient, other_monomial, Ring.insert(coefficient, monomial, rest)})

def Ring.add(+left: Ring.Poly, +right: Ring.Poly) -> Ring.Poly:
  match left:
    case NoTerms{}:
      right
    case Term{coefficient, monomial, rest}:
      Ring.insert(coefficient, monomial, Ring.add(rest, right))

def Ring.scale(+coefficient: Nat, +monomial: Ring.Monomial, +poly: Ring.Poly) -> Ring.Poly:
  match poly:
    case NoTerms{}:
      NoTerms{}
    case Term{other_coefficient, other_monomial, rest}:
      Ring.insert(Nat.mul(coefficient, other_coefficient), Ring.merge(monomial, other_monomial),
        Ring.scale(coefficient, monomial, rest))

def Ring.mul(+left: Ring.Poly, +right: Ring.Poly) -> Ring.Poly:
  match left:
    case NoTerms{}:
      NoTerms{}
    case Term{coefficient, monomial, rest}:
      Ring.add(Ring.scale(coefficient, monomial, right), Ring.mul(rest, right))

def Ring.norm(expr: Ring.Expr) -> Ring.Poly:
  match expr:
    case Atom{index}:
      Term{1n, Times{index, One{}}, NoTerms{}}
    case Constant{value}:
      Ring.insert(value, One{}, NoTerms{})
    case Next{body}:
      Ring.insert(1n, One{}, Ring.norm(body))
    case Sum{left, right}:
      Ring.add(Ring.norm(left), Ring.norm(right))
    case Product{left, right}:
      Ring.mul(Ring.norm(left), Ring.norm(right))

def Ring.IsEqual(order: Cmp) -> Type:
  match order:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Empty

def Ring.less_not_equal(proof: {LT{} == EQ{} : Cmp}) -> Empty:
  +flipped: {EQ{} == LT{} : Cmp} = Equal.sym(Cmp, LT{}, EQ{}, proof)
  %flipped : Ring.IsEqual(_)
  Unit{}

def Ring.greater_not_equal(proof: {GT{} == EQ{} : Cmp}) -> Empty:
  +flipped: {EQ{} == GT{} : Cmp} = Equal.sym(Cmp, GT{}, EQ{}, proof)
  %flipped : Ring.IsEqual(_)
  Unit{}

def Ring.cmp_equal(+left: Nat, +right: Nat, proof: {Nat.cmp(left, right) == EQ{} : Cmp}) -> {left == right : Nat}:
  match left right:
    case 0n 0n:
      {==}
    case 0n 1n+right_previous:
      Empty.absurd({0n == 1n+right_previous : Nat}, Ring.less_not_equal(proof))
    case 1n+left_previous 0n:
      Empty.absurd({1n+left_previous == 0n : Nat}, Ring.greater_not_equal(proof))
    case 1n+left_previous 1n+right_previous:
      Equal.cong(Nat, Nat, z => 1n+z, left_previous, right_previous, Ring.cmp_equal(left_previous, right_previous, proof))

def Ring.then_equal(+first: Cmp, +second: Cmp, proof: {Ring.then(first, second) == EQ{} : Cmp}) ->
  {first == EQ{} : Cmp} & {second == EQ{} : Cmp}:
  match first:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp} & {second == EQ{} : Cmp}, Ring.less_not_equal(proof))
    case EQ{}:
      ({==}, proof)
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp} & {second == EQ{} : Cmp}, Ring.greater_not_equal(proof))

def Ring.times_congruent(+left_index: Nat, +left_rest: Ring.Monomial, +right_index: Nat, +right_rest: Ring.Monomial,
  index_equal: {left_index == right_index : Nat}, rest_equal: {left_rest == right_rest : Ring.Monomial}) ->
  {Times{left_index, left_rest} == Times{right_index, right_rest} : Ring.Monomial}:
  %index_equal : {Times{left_index, left_rest} == Times{_, right_rest} : Ring.Monomial}
  %rest_equal : {Times{left_index, left_rest} == Times{left_index, _} : Ring.Monomial}
  {==}

def Ring.compare_equal(+left: Ring.Monomial, +right: Ring.Monomial, +proof: {Ring.compare(left, right) == EQ{} : Cmp}) ->
  {left == right : Ring.Monomial}:
  match left right:
    case One{} One{}:
      {==}
    case One{} Times{index, rest}:
      Empty.absurd({One{} == Times{index, rest} : Ring.Monomial}, Ring.less_not_equal(proof))
    case Times{index, rest} One{}:
      Empty.absurd({Times{index, rest} == One{} : Ring.Monomial}, Ring.greater_not_equal(proof))
    case Times{+left_index, +left_rest} Times{+right_index, +right_rest}:
      Ring.times_congruent(left_index, left_rest, right_index, right_rest,
        Ring.cmp_equal(left_index, right_index,
          Pair.fst({Nat.cmp(left_index, right_index) == EQ{} : Cmp}, {Ring.compare(left_rest, right_rest) == EQ{} : Cmp},
            Ring.then_equal(Nat.cmp(left_index, right_index), Ring.compare(left_rest, right_rest), proof))),
        Ring.compare_equal(left_rest, right_rest,
          Pair.snd({Nat.cmp(left_index, right_index) == EQ{} : Cmp}, {Ring.compare(left_rest, right_rest) == EQ{} : Cmp},
            Ring.then_equal(Nat.cmp(left_index, right_index), Ring.compare(left_rest, right_rest), proof))))

def Ring.choose_monomial_sound(+values: Ring.Values, order: Cmp, +first: Ring.Monomial, +second: Ring.Monomial, -target: Nat,
  first_sound: {Ring.eval_monomial(values, first) == target : Nat},
  second_sound: {Ring.eval_monomial(values, second) == target : Nat}) ->
  {Ring.eval_monomial(values, Ring.choose_monomial(order, first, first, second)) == target : Nat}:
  match order:
    case LT{}:
      first_sound
    case EQ{}:
      first_sound
    case GT{}:
      second_sound

def Ring.merge_sound(+values: Ring.Values, +left: Ring.Monomial, +right: Ring.Monomial) ->
  {Ring.eval_monomial(values, Ring.merge(left, right)) == Nat.mul(Ring.eval_monomial(values, left), Ring.eval_monomial(values, right)) : Nat}:
  match left right:
    case One{} One{}:
      {==}
    case One{} Times{+index, +rest}:
      Equal.sym(Nat, Nat.mul(1n, Ring.eval_monomial(values, Times{index, rest})), Ring.eval_monomial(values, Times{index, rest}),
        N.Natural.one_mul(Ring.eval_monomial(values, Times{index, rest})))
    case Times{+index, +rest} One{}:
      Equal.sym(Nat, Nat.mul(Ring.eval_monomial(values, Times{index, rest}), 1n), Ring.eval_monomial(values, Times{index, rest}),
        N.Natural.mul_one(Ring.eval_monomial(values, Times{index, rest})))
    case Times{+left_index, +left_rest} Times{+right_index, +right_rest}:
      +x: Nat = Ring.lookup(values, left_index)
      +y: Nat = Ring.lookup(values, right_index)
      +left_value: Nat = Ring.eval_monomial(values, Times{left_index, left_rest})
      +right_value: Nat = Ring.eval_monomial(values, Times{right_index, right_rest})
      +left_rest_value: Nat = Ring.eval_monomial(values, left_rest)
      +right_rest_value: Nat = Ring.eval_monomial(values, right_rest)
      Ring.choose_monomial_sound(values, Nat.cmp(left_index, right_index),
        Times{left_index, Ring.merge(left_rest, Times{right_index, right_rest})},
        Times{right_index, Ring.merge(Times{left_index, left_rest}, right_rest)},
        Nat.mul(left_value, right_value),
        Equal.trans(Nat,
          Nat.mul(x, Ring.eval_monomial(values, Ring.merge(left_rest, Times{right_index, right_rest}))),
          Nat.mul(x, Nat.mul(left_rest_value, right_value)),
          Nat.mul(left_value, right_value),
          Equal.cong(Nat, Nat, z => Nat.mul(x, z),
            Ring.eval_monomial(values, Ring.merge(left_rest, Times{right_index, right_rest})), Nat.mul(left_rest_value, right_value),
            Ring.merge_sound(values, left_rest, Times{right_index, right_rest})),
          Equal.sym(Nat, Nat.mul(Nat.mul(x, left_rest_value), right_value), Nat.mul(x, Nat.mul(left_rest_value, right_value)),
            N.Natural.mul_associative(x, left_rest_value, right_value))),
        Equal.trans(Nat,
          Nat.mul(y, Ring.eval_monomial(values, Ring.merge(Times{left_index, left_rest}, right_rest))),
          Nat.mul(y, Nat.mul(left_value, right_rest_value)),
          Nat.mul(left_value, right_value),
          Equal.cong(Nat, Nat, z => Nat.mul(y, z),
            Ring.eval_monomial(values, Ring.merge(Times{left_index, left_rest}, right_rest)), Nat.mul(left_value, right_rest_value),
            Ring.merge_sound(values, Times{left_index, left_rest}, right_rest)),
          N.Natural.mul_swap(y, left_value, right_rest_value)))

def Ring.insert_sound_at(+values: Ring.Values, +coefficient: Nat, +monomial: Ring.Monomial,
  +other_coefficient: Nat, +other_monomial: Ring.Monomial, +rest: Ring.Poly,
  order: Cmp, +order_is: {Ring.compare(monomial, other_monomial) == order : Cmp},
  rest_sound: {Ring.eval_poly(values, Ring.insert(coefficient, monomial, rest)) ==
    Nat.add(Nat.mul(coefficient, Ring.eval_monomial(values, monomial)), Ring.eval_poly(values, rest)) : Nat}) ->
  {Ring.eval_poly(values, Ring.choose_poly(order,
      Term{coefficient, monomial, Term{other_coefficient, other_monomial, rest}},
      Term{Nat.add(coefficient, other_coefficient), other_monomial, rest},
      Term{other_coefficient, other_monomial, Ring.insert(coefficient, monomial, rest)})) ==
   Nat.add(Nat.mul(coefficient, Ring.eval_monomial(values, monomial)),
     Nat.add(Nat.mul(other_coefficient, Ring.eval_monomial(values, other_monomial)), Ring.eval_poly(values, rest))) : Nat}:
  match order:
    case LT{}:
      {==}
    case EQ{}:
      +other_value: Nat = Ring.eval_monomial(values, other_monomial)
      +rest_value: Nat = Ring.eval_poly(values, rest)
      +same: {other_monomial == monomial : Ring.Monomial} =
        Equal.sym(Ring.Monomial, monomial, other_monomial, Ring.compare_equal(monomial, other_monomial, order_is))
      %same : {Nat.add(Nat.mul(Nat.add(coefficient, other_coefficient), other_value), rest_value) ==
        Nat.add(Nat.mul(coefficient, Ring.eval_monomial(values, _)), Nat.add(Nat.mul(other_coefficient, other_value), rest_value)) : Nat}
      Equal.trans(Nat,
        Nat.add(Nat.mul(Nat.add(coefficient, other_coefficient), other_value), rest_value),
        Nat.add(Nat.add(Nat.mul(coefficient, other_value), Nat.mul(other_coefficient, other_value)), rest_value),
        Nat.add(Nat.mul(coefficient, other_value), Nat.add(Nat.mul(other_coefficient, other_value), rest_value)),
        Equal.cong(Nat, Nat, z => Nat.add(z, rest_value),
          Nat.mul(Nat.add(coefficient, other_coefficient), other_value),
          Nat.add(Nat.mul(coefficient, other_value), Nat.mul(other_coefficient, other_value)),
          N.Natural.mul_add_left(coefficient, other_coefficient, other_value)),
        N.Natural.add_associative(Nat.mul(coefficient, other_value), Nat.mul(other_coefficient, other_value), rest_value))
    case GT{}:
      +value: Nat = Ring.eval_monomial(values, monomial)
      +other_value: Nat = Ring.eval_monomial(values, other_monomial)
      +rest_value: Nat = Ring.eval_poly(values, rest)
      Equal.trans(Nat,
        Nat.add(Nat.mul(other_coefficient, other_value), Ring.eval_poly(values, Ring.insert(coefficient, monomial, rest))),
        Nat.add(Nat.mul(other_coefficient, other_value), Nat.add(Nat.mul(coefficient, value), rest_value)),
        Nat.add(Nat.mul(coefficient, value), Nat.add(Nat.mul(other_coefficient, other_value), rest_value)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(other_coefficient, other_value), z),
          Ring.eval_poly(values, Ring.insert(coefficient, monomial, rest)), Nat.add(Nat.mul(coefficient, value), rest_value),
          rest_sound),
        N.Natural.add_swap(Nat.mul(other_coefficient, other_value), Nat.mul(coefficient, value), rest_value))

def Ring.insert_sound(+values: Ring.Values, +coefficient: Nat, +monomial: Ring.Monomial, +poly: Ring.Poly) ->
  {Ring.eval_poly(values, Ring.insert(coefficient, monomial, poly)) ==
   Nat.add(Nat.mul(coefficient, Ring.eval_monomial(values, monomial)), Ring.eval_poly(values, poly)) : Nat}:
  match coefficient:
    case 0n:
      {==}
    case 1n+previous:
      match poly:
        case NoTerms{}:
          {==}
        case Term{+other_coefficient, +other_monomial, +rest}:
          Ring.insert_sound_at(values, 1n+previous, monomial, other_coefficient, other_monomial, rest,
            Ring.compare(monomial, other_monomial), {==},
            Ring.insert_sound(values, 1n+previous, monomial, rest))

def Ring.add_sound(+values: Ring.Values, +left: Ring.Poly, +right: Ring.Poly) ->
  {Ring.eval_poly(values, Ring.add(left, right)) == Nat.add(Ring.eval_poly(values, left), Ring.eval_poly(values, right)) : Nat}:
  match left:
    case NoTerms{}:
      {==}
    case Term{+coefficient, +monomial, +rest}:
      +term_value: Nat = Nat.mul(coefficient, Ring.eval_monomial(values, monomial))
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.insert(coefficient, monomial, Ring.add(rest, right))),
        Nat.add(term_value, Nat.add(Ring.eval_poly(values, rest), Ring.eval_poly(values, right))),
        Nat.add(Nat.add(term_value, Ring.eval_poly(values, rest)), Ring.eval_poly(values, right)),
        Equal.trans(Nat,
          Ring.eval_poly(values, Ring.insert(coefficient, monomial, Ring.add(rest, right))),
          Nat.add(term_value, Ring.eval_poly(values, Ring.add(rest, right))),
          Nat.add(term_value, Nat.add(Ring.eval_poly(values, rest), Ring.eval_poly(values, right))),
          Ring.insert_sound(values, coefficient, monomial, Ring.add(rest, right)),
          Equal.cong(Nat, Nat, z => Nat.add(term_value, z),
            Ring.eval_poly(values, Ring.add(rest, right)), Nat.add(Ring.eval_poly(values, rest), Ring.eval_poly(values, right)),
            Ring.add_sound(values, rest, right))),
        Equal.sym(Nat,
          Nat.add(Nat.add(term_value, Ring.eval_poly(values, rest)), Ring.eval_poly(values, right)),
          Nat.add(term_value, Nat.add(Ring.eval_poly(values, rest), Ring.eval_poly(values, right))),
          N.Natural.add_associative(term_value, Ring.eval_poly(values, rest), Ring.eval_poly(values, right))))

def Ring.scale_sound(+values: Ring.Values, +coefficient: Nat, +monomial: Ring.Monomial, +poly: Ring.Poly) ->
  {Ring.eval_poly(values, Ring.scale(coefficient, monomial, poly)) ==
   Nat.mul(Nat.mul(coefficient, Ring.eval_monomial(values, monomial)), Ring.eval_poly(values, poly)) : Nat}:
  match poly:
    case NoTerms{}:
      +factor: Nat = Nat.mul(coefficient, Ring.eval_monomial(values, monomial))
      Equal.sym(Nat, Nat.mul(factor, 0n), 0n, N.Natural.mul_zero(factor))
    case Term{+other_coefficient, +other_monomial, +rest}:
      +factor: Nat = Nat.mul(coefficient, Ring.eval_monomial(values, monomial))
      +value: Nat = Ring.eval_monomial(values, monomial)
      +other_value: Nat = Ring.eval_monomial(values, other_monomial)
      +rest_value: Nat = Ring.eval_poly(values, rest)
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.insert(Nat.mul(coefficient, other_coefficient), Ring.merge(monomial, other_monomial),
          Ring.scale(coefficient, monomial, rest))),
        Nat.add(Nat.mul(Nat.mul(coefficient, other_coefficient), Ring.eval_monomial(values, Ring.merge(monomial, other_monomial))),
          Ring.eval_poly(values, Ring.scale(coefficient, monomial, rest))),
        Nat.mul(factor, Nat.add(Nat.mul(other_coefficient, other_value), rest_value)),
        Ring.insert_sound(values, Nat.mul(coefficient, other_coefficient), Ring.merge(monomial, other_monomial),
          Ring.scale(coefficient, monomial, rest)),
        Equal.trans(Nat,
          Nat.add(Nat.mul(Nat.mul(coefficient, other_coefficient), Ring.eval_monomial(values, Ring.merge(monomial, other_monomial))),
            Ring.eval_poly(values, Ring.scale(coefficient, monomial, rest))),
          Nat.add(Nat.mul(factor, Nat.mul(other_coefficient, other_value)), Nat.mul(factor, rest_value)),
          Nat.mul(factor, Nat.add(Nat.mul(other_coefficient, other_value), rest_value)),
          N.Natural.eq_add_congruent(
            Nat.mul(Nat.mul(coefficient, other_coefficient), Ring.eval_monomial(values, Ring.merge(monomial, other_monomial))),
            Ring.eval_poly(values, Ring.scale(coefficient, monomial, rest)),
            Nat.mul(factor, Nat.mul(other_coefficient, other_value)),
            Nat.mul(factor, rest_value),
            Equal.trans(Nat,
              Nat.mul(Nat.mul(coefficient, other_coefficient), Ring.eval_monomial(values, Ring.merge(monomial, other_monomial))),
              Nat.mul(Nat.mul(coefficient, other_coefficient), Nat.mul(value, other_value)),
              Nat.mul(factor, Nat.mul(other_coefficient, other_value)),
              Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(coefficient, other_coefficient), z),
                Ring.eval_monomial(values, Ring.merge(monomial, other_monomial)), Nat.mul(value, other_value),
                Ring.merge_sound(values, monomial, other_monomial)),
              N.Natural.mul_four_middle_commute(coefficient, other_coefficient, value, other_value)),
            Ring.scale_sound(values, coefficient, monomial, rest)),
          Equal.sym(Nat,
            Nat.mul(factor, Nat.add(Nat.mul(other_coefficient, other_value), rest_value)),
            Nat.add(Nat.mul(factor, Nat.mul(other_coefficient, other_value)), Nat.mul(factor, rest_value)),
            N.Natural.mul_add_right(factor, Nat.mul(other_coefficient, other_value), rest_value))))

def Ring.mul_sound(+values: Ring.Values, +left: Ring.Poly, +right: Ring.Poly) ->
  {Ring.eval_poly(values, Ring.mul(left, right)) == Nat.mul(Ring.eval_poly(values, left), Ring.eval_poly(values, right)) : Nat}:
  match left:
    case NoTerms{}:
      {==}
    case Term{+coefficient, +monomial, +rest}:
      +factor: Nat = Nat.mul(coefficient, Ring.eval_monomial(values, monomial))
      +right_value: Nat = Ring.eval_poly(values, right)
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.add(Ring.scale(coefficient, monomial, right), Ring.mul(rest, right))),
        Nat.add(Nat.mul(factor, right_value), Nat.mul(Ring.eval_poly(values, rest), right_value)),
        Nat.mul(Nat.add(factor, Ring.eval_poly(values, rest)), right_value),
        Equal.trans(Nat,
          Ring.eval_poly(values, Ring.add(Ring.scale(coefficient, monomial, right), Ring.mul(rest, right))),
          Nat.add(Ring.eval_poly(values, Ring.scale(coefficient, monomial, right)), Ring.eval_poly(values, Ring.mul(rest, right))),
          Nat.add(Nat.mul(factor, right_value), Nat.mul(Ring.eval_poly(values, rest), right_value)),
          Ring.add_sound(values, Ring.scale(coefficient, monomial, right), Ring.mul(rest, right)),
          N.Natural.eq_add_congruent(
            Ring.eval_poly(values, Ring.scale(coefficient, monomial, right)), Ring.eval_poly(values, Ring.mul(rest, right)),
            Nat.mul(factor, right_value), Nat.mul(Ring.eval_poly(values, rest), right_value),
            Ring.scale_sound(values, coefficient, monomial, right), Ring.mul_sound(values, rest, right))),
        Equal.sym(Nat,
          Nat.mul(Nat.add(factor, Ring.eval_poly(values, rest)), right_value),
          Nat.add(Nat.mul(factor, right_value), Nat.mul(Ring.eval_poly(values, rest), right_value)),
          N.Natural.mul_add_left(factor, Ring.eval_poly(values, rest), right_value)))

def Ring.norm_sound(+values: Ring.Values, +expr: Ring.Expr) -> {Ring.eval_poly(values, Ring.norm(expr)) == Ring.eval(values, expr) : Nat}:
  match expr:
    case Atom{+index}:
      +x: Nat = Ring.lookup(values, index)
      Equal.trans(Nat,
        Nat.add(Nat.mul(1n, Nat.mul(x, 1n)), 0n), Nat.mul(1n, Nat.mul(x, 1n)), x,
        N.Natural.add_zero(Nat.mul(1n, Nat.mul(x, 1n))),
        Equal.trans(Nat, Nat.mul(1n, Nat.mul(x, 1n)), Nat.mul(x, 1n), x,
          N.Natural.one_mul(Nat.mul(x, 1n)), N.Natural.mul_one(x)))
    case Constant{+value}:
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.insert(value, One{}, NoTerms{})), Nat.add(Nat.mul(value, 1n), 0n), value,
        Ring.insert_sound(values, value, One{}, NoTerms{}),
        Equal.trans(Nat, Nat.add(Nat.mul(value, 1n), 0n), Nat.mul(value, 1n), value,
          N.Natural.add_zero(Nat.mul(value, 1n)), N.Natural.mul_one(value)))
    case Next{+body}:
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.insert(1n, One{}, Ring.norm(body))),
        1n+Ring.eval_poly(values, Ring.norm(body)),
        1n+Ring.eval(values, body),
        Ring.insert_sound(values, 1n, One{}, Ring.norm(body)),
        Equal.cong(Nat, Nat, z => 1n+z, Ring.eval_poly(values, Ring.norm(body)), Ring.eval(values, body),
          Ring.norm_sound(values, body)))
    case Sum{+left, +right}:
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.add(Ring.norm(left), Ring.norm(right))),
        Nat.add(Ring.eval_poly(values, Ring.norm(left)), Ring.eval_poly(values, Ring.norm(right))),
        Nat.add(Ring.eval(values, left), Ring.eval(values, right)),
        Ring.add_sound(values, Ring.norm(left), Ring.norm(right)),
        N.Natural.eq_add_congruent(
          Ring.eval_poly(values, Ring.norm(left)), Ring.eval_poly(values, Ring.norm(right)),
          Ring.eval(values, left), Ring.eval(values, right),
          Ring.norm_sound(values, left), Ring.norm_sound(values, right)))
    case Product{+left, +right}:
      Equal.trans(Nat,
        Ring.eval_poly(values, Ring.mul(Ring.norm(left), Ring.norm(right))),
        Nat.mul(Ring.eval_poly(values, Ring.norm(left)), Ring.eval_poly(values, Ring.norm(right))),
        Nat.mul(Ring.eval(values, left), Ring.eval(values, right)),
        Ring.mul_sound(values, Ring.norm(left), Ring.norm(right)),
        N.Natural.eq_mul_congruent(
          Ring.eval_poly(values, Ring.norm(left)), Ring.eval_poly(values, Ring.norm(right)),
          Ring.eval(values, left), Ring.eval(values, right),
          Ring.norm_sound(values, left), Ring.norm_sound(values, right)))

def Ring.equal(+values: Ring.Values, +left: Ring.Expr, +right: Ring.Expr,
  same: {Ring.norm(left) == Ring.norm(right) : Ring.Poly}) ->
  {Ring.eval(values, left) == Ring.eval(values, right) : Nat}:
  Equal.trans(Nat,
    Ring.eval(values, left), Ring.eval_poly(values, Ring.norm(left)), Ring.eval(values, right),
    Equal.sym(Nat, Ring.eval_poly(values, Ring.norm(left)), Ring.eval(values, left), Ring.norm_sound(values, left)),
    Equal.trans(Nat,
      Ring.eval_poly(values, Ring.norm(left)), Ring.eval_poly(values, Ring.norm(right)), Ring.eval(values, right),
      Equal.cong(Ring.Poly, Nat, z => Ring.eval_poly(values, z), Ring.norm(left), Ring.norm(right), same),
      Ring.norm_sound(values, right)))

def Ring.overshoot(base: Nat, +slack: Nat, le: N.Natural.Le(Nat.add(base, 1n+slack), base)) -> Empty:
  match base:
    case 0n:
      match le:
    case 1n+previous:
      Ring.overshoot(previous, slack, le)

def Ring.refute(+values: Ring.Values, +left: Ring.Expr, +right: Ring.Expr, +slack: Ring.Expr,
  le: N.Natural.Le(Ring.eval(values, left), Ring.eval(values, right)),
  same: {Ring.norm(left) == Ring.norm(Sum{right, Next{slack}}) : Ring.Poly}) -> Empty:
  Ring.overshoot(Ring.eval(values, right), Ring.eval(values, slack),
    N.Natural.le_congruent(Ring.eval(values, left), Ring.eval(values, right),
      Nat.add(Ring.eval(values, right), 1n+Ring.eval(values, slack)), Ring.eval(values, right),
      le, Ring.equal(values, left, Sum{right, Next{slack}}, same), {==}))

def Ring.cancel(+values: Ring.Values, +left: Ring.Expr, +right: Ring.Expr, +common: Ring.Expr, +smaller: Ring.Expr, +larger: Ring.Expr,
  le: N.Natural.Le(Ring.eval(values, left), Ring.eval(values, right)),
  left_same: {Ring.norm(left) == Ring.norm(Sum{common, smaller}) : Ring.Poly},
  right_same: {Ring.norm(right) == Ring.norm(Sum{common, larger}) : Ring.Poly}) ->
  N.Natural.Le(Ring.eval(values, smaller), Ring.eval(values, larger)):
  N.Natural.le_add_left_cancel(Ring.eval(values, common), Ring.eval(values, smaller), Ring.eval(values, larger),
    N.Natural.le_congruent(Ring.eval(values, left), Ring.eval(values, right),
      Nat.add(Ring.eval(values, common), Ring.eval(values, smaller)), Nat.add(Ring.eval(values, common), Ring.eval(values, larger)),
      le, Ring.equal(values, left, Sum{common, smaller}, left_same), Ring.equal(values, right, Sum{common, larger}, right_same)))
