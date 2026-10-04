import Base
import ./Field.bend as K
import ./FieldAlgebra.bend as A
import ./Ring.bend as G

type FieldRing.Values<-F: Kind(&2)> is Data:
  NoValues{}
  Value{head: F, tail: FieldRing.Values<F>}

def FieldRing.of_nat(~F: Kind(&2), ~field: K.Field<F>, n: Nat) -> F:
  match n:
    case 0n:
      A.Algebra.zero(~F, ~field)
    case 1n+previous:
      A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.of_nat(~F, ~field, previous))

def FieldRing.lookup(~F: Kind(&2), ~field: K.Field<F>, values: FieldRing.Values<F>, index: Nat) -> F:
  match values:
    case NoValues{}:
      A.Algebra.zero(~F, ~field)
    case Value{head, tail}:
      match index:
        case 0n:
          head
        case 1n+previous:
          FieldRing.lookup(~F, ~field, tail, previous)

def FieldRing.eval_monomial(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, monomial: G.Ring.Monomial) -> F:
  match monomial:
    case G.One{}:
      A.Algebra.one(~F, ~field)
    case G.Times{index, rest}:
      A.Algebra.mul(~F, ~field, FieldRing.lookup(~F, ~field, values, index), FieldRing.eval_monomial(~F, ~field, values, rest))

def FieldRing.eval_poly(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, poly: G.Ring.Poly) -> F:
  match poly:
    case G.NoTerms{}:
      A.Algebra.zero(~F, ~field)
    case G.Term{coefficient, monomial, rest}:
      A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial)), FieldRing.eval_poly(~F, ~field, values, rest))

def FieldRing.eval(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, expr: G.Ring.Expr) -> F:
  match expr:
    case G.Atom{index}:
      FieldRing.lookup(~F, ~field, values, index)
    case G.Constant{value}:
      FieldRing.of_nat(~F, ~field, value)
    case G.Next{body}:
      A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.eval(~F, ~field, values, body))
    case G.Sum{left, right}:
      A.Algebra.add(~F, ~field, FieldRing.eval(~F, ~field, values, left), FieldRing.eval(~F, ~field, values, right))
    case G.Product{left, right}:
      A.Algebra.mul(~F, ~field, FieldRing.eval(~F, ~field, values, left), FieldRing.eval(~F, ~field, values, right))

def FieldRing.add_swap(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.add(~F, ~field, b, c)), A.Algebra.add(~F, ~field, b, A.Algebra.add(~F, ~field, a, c))):
  A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.add(~F, ~field, b, c)), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, b), c), A.Algebra.add(~F, ~field, b, A.Algebra.add(~F, ~field, a, c)),
    A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, b), c), A.Algebra.add(~F, ~field, a, A.Algebra.add(~F, ~field, b, c)), A.Algebra.add_associates(~F, ~field, a, b, c)),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, a, b), c), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, b, a), c), A.Algebra.add(~F, ~field, b, A.Algebra.add(~F, ~field, a, c)),
      A.Algebra.add_respects_left(~F, ~field, A.Algebra.add(~F, ~field, a, b), A.Algebra.add(~F, ~field, b, a), c, A.Algebra.add_commutes(~F, ~field, a, b)),
      A.Algebra.add_associates(~F, ~field, b, a, c)))

def FieldRing.mul_swap(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, b, c)), A.Algebra.mul(~F, ~field, b, A.Algebra.mul(~F, ~field, a, c))):
  A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, b, c)), A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, b), c), A.Algebra.mul(~F, ~field, b, A.Algebra.mul(~F, ~field, a, c)),
    A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, b), c), A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, b, c)), A.Algebra.mul_associates(~F, ~field, a, b, c)),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, b), c), A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, b, a), c), A.Algebra.mul(~F, ~field, b, A.Algebra.mul(~F, ~field, a, c)),
      A.Algebra.mul_respects_left(~F, ~field, A.Algebra.mul(~F, ~field, a, b), A.Algebra.mul(~F, ~field, b, a), c, A.Algebra.mul_commutes(~F, ~field, a, b)),
      A.Algebra.mul_associates(~F, ~field, b, a, c)))

def FieldRing.mul_four(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, +d: F) -> A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, b), A.Algebra.mul(~F, ~field, c, d)), A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, c), A.Algebra.mul(~F, ~field, b, d))):
  A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, b), A.Algebra.mul(~F, ~field, c, d)), A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, c, A.Algebra.mul(~F, ~field, b, d))), A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, c), A.Algebra.mul(~F, ~field, b, d)),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, b), A.Algebra.mul(~F, ~field, c, d)), A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, b, A.Algebra.mul(~F, ~field, c, d))), A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, c, A.Algebra.mul(~F, ~field, b, d))),
      A.Algebra.mul_associates(~F, ~field, a, b, A.Algebra.mul(~F, ~field, c, d)),
      A.Algebra.mul_respects_right(~F, ~field, A.Algebra.mul(~F, ~field, b, A.Algebra.mul(~F, ~field, c, d)), A.Algebra.mul(~F, ~field, c, A.Algebra.mul(~F, ~field, b, d)), a, FieldRing.mul_swap(~F, ~field, b, c, d))),
    A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, a, c), A.Algebra.mul(~F, ~field, b, d)), A.Algebra.mul(~F, ~field, a, A.Algebra.mul(~F, ~field, c, A.Algebra.mul(~F, ~field, b, d))), A.Algebra.mul_associates(~F, ~field, a, c, A.Algebra.mul(~F, ~field, b, d))))

def FieldRing.of_nat_add(~F: Kind(&2), ~field: K.Field<F>, +a: Nat, +b: Nat) ->
  A.Algebra.Same(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(a, b)), A.Algebra.add(~F, ~field, FieldRing.of_nat(~F, ~field, a), FieldRing.of_nat(~F, ~field, b))):
  match a:
    case 0n:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), FieldRing.of_nat(~F, ~field, b)), FieldRing.of_nat(~F, ~field, b), A.Algebra.zero_add(~F, ~field, FieldRing.of_nat(~F, ~field, b)))
    case 1n+previous:
      A.Algebra.same_transitive(~F, ~field,
        A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.of_nat(~F, ~field, Nat.add(previous, b))),
        A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, FieldRing.of_nat(~F, ~field, previous), FieldRing.of_nat(~F, ~field, b))),
        A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.of_nat(~F, ~field, previous)), FieldRing.of_nat(~F, ~field, b)),
        A.Algebra.add_respects_right(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(previous, b)), A.Algebra.add(~F, ~field, FieldRing.of_nat(~F, ~field, previous), FieldRing.of_nat(~F, ~field, b)), A.Algebra.one(~F, ~field),
          FieldRing.of_nat_add(~F, ~field, previous, b)),
        A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.of_nat(~F, ~field, previous)), FieldRing.of_nat(~F, ~field, b)), A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.add(~F, ~field, FieldRing.of_nat(~F, ~field, previous), FieldRing.of_nat(~F, ~field, b))),
          A.Algebra.add_associates(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.of_nat(~F, ~field, previous), FieldRing.of_nat(~F, ~field, b))))

def FieldRing.of_nat_mul(~F: Kind(&2), ~field: K.Field<F>, +a: Nat, +b: Nat) ->
  A.Algebra.Same(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.mul(a, b)), A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, a), FieldRing.of_nat(~F, ~field, b))):
  match a:
    case 0n:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), FieldRing.of_nat(~F, ~field, b)), A.Algebra.zero(~F, ~field), A.Algebra.zero_mul(~F, ~field, FieldRing.of_nat(~F, ~field, b)))
    case 1n+previous:
      +x: F = FieldRing.of_nat(~F, ~field, previous)
      +y: F = FieldRing.of_nat(~F, ~field, b)
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.of_nat(~F, ~field, Nat.add(b, Nat.mul(previous, b))),
        A.Algebra.add(~F, ~field, y, A.Algebra.mul(~F, ~field, x, y)),
        A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), x), y),
        A.Algebra.same_transitive(~F, ~field,
          FieldRing.of_nat(~F, ~field, Nat.add(b, Nat.mul(previous, b))),
          A.Algebra.add(~F, ~field, y, FieldRing.of_nat(~F, ~field, Nat.mul(previous, b))),
          A.Algebra.add(~F, ~field, y, A.Algebra.mul(~F, ~field, x, y)),
          FieldRing.of_nat_add(~F, ~field, b, Nat.mul(previous, b)),
          A.Algebra.add_respects_right(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.mul(previous, b)), A.Algebra.mul(~F, ~field, x, y), y, FieldRing.of_nat_mul(~F, ~field, previous, b))),
        A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), x), y), A.Algebra.add(~F, ~field, y, A.Algebra.mul(~F, ~field, x, y)),
          A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), x), y), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), y), A.Algebra.mul(~F, ~field, x, y)), A.Algebra.add(~F, ~field, y, A.Algebra.mul(~F, ~field, x, y)),
            A.Algebra.distributes_right(~F, ~field, A.Algebra.one(~F, ~field), x, y),
            A.Algebra.add_respects_left(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), y), y, A.Algebra.mul(~F, ~field, x, y), A.Algebra.one_mul(~F, ~field, y)))))

def FieldRing.choose_monomial_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, order: Cmp, +first: G.Ring.Monomial, +second: G.Ring.Monomial, +target: F,
  first_sound: A.Algebra.Same(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, first), target),
  second_sound: A.Algebra.Same(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, second), target)) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, G.Ring.choose_monomial(order, first, first, second)), target):
  match order:
    case LT{}:
      first_sound
    case EQ{}:
      first_sound
    case GT{}:
      second_sound

def FieldRing.merge_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +left: G.Ring.Monomial, +right: G.Ring.Monomial) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(left, right)), A.Algebra.mul(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, left), FieldRing.eval_monomial(~F, ~field, values, right))):
  match left right:
    case G.One{} G.One{}:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.one(~F, ~field)), A.Algebra.one(~F, ~field), A.Algebra.mul_one(~F, ~field, A.Algebra.one(~F, ~field)))
    case G.One{} G.Times{+index, +rest}:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.eval_monomial(~F, ~field, values, G.Times{index, rest})), FieldRing.eval_monomial(~F, ~field, values, G.Times{index, rest}),
        A.Algebra.one_mul(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, G.Times{index, rest})))
    case G.Times{+index, +rest} G.One{}:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, G.Times{index, rest}), A.Algebra.one(~F, ~field)), FieldRing.eval_monomial(~F, ~field, values, G.Times{index, rest}),
        A.Algebra.mul_one(~F, ~field, FieldRing.eval_monomial(~F, ~field, values, G.Times{index, rest})))
    case G.Times{+left_index, +left_rest} G.Times{+right_index, +right_rest}:
      +x: F = FieldRing.lookup(~F, ~field, values, left_index)
      +y: F = FieldRing.lookup(~F, ~field, values, right_index)
      +left_value: F = FieldRing.eval_monomial(~F, ~field, values, G.Times{left_index, left_rest})
      +right_value: F = FieldRing.eval_monomial(~F, ~field, values, G.Times{right_index, right_rest})
      +left_rest_value: F = FieldRing.eval_monomial(~F, ~field, values, left_rest)
      +right_rest_value: F = FieldRing.eval_monomial(~F, ~field, values, right_rest)
      FieldRing.choose_monomial_sound(~F, ~field, values, Nat.cmp(left_index, right_index),
        G.Times{left_index, G.Ring.merge(left_rest, G.Times{right_index, right_rest})},
        G.Times{right_index, G.Ring.merge(G.Times{left_index, left_rest}, right_rest)},
        A.Algebra.mul(~F, ~field, left_value, right_value),
        A.Algebra.same_transitive(~F, ~field,
          A.Algebra.mul(~F, ~field, x, FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(left_rest, G.Times{right_index, right_rest}))),
          A.Algebra.mul(~F, ~field, x, A.Algebra.mul(~F, ~field, left_rest_value, right_value)),
          A.Algebra.mul(~F, ~field, left_value, right_value),
          A.Algebra.mul_respects_right(~F, ~field,
            FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(left_rest, G.Times{right_index, right_rest})), A.Algebra.mul(~F, ~field, left_rest_value, right_value), x,
            FieldRing.merge_sound(~F, ~field, values, left_rest, G.Times{right_index, right_rest})),
          A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, x, left_rest_value), right_value), A.Algebra.mul(~F, ~field, x, A.Algebra.mul(~F, ~field, left_rest_value, right_value)),
            A.Algebra.mul_associates(~F, ~field, x, left_rest_value, right_value))),
        A.Algebra.same_transitive(~F, ~field,
          A.Algebra.mul(~F, ~field, y, FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(G.Times{left_index, left_rest}, right_rest))),
          A.Algebra.mul(~F, ~field, y, A.Algebra.mul(~F, ~field, left_value, right_rest_value)),
          A.Algebra.mul(~F, ~field, left_value, right_value),
          A.Algebra.mul_respects_right(~F, ~field,
            FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(G.Times{left_index, left_rest}, right_rest)), A.Algebra.mul(~F, ~field, left_value, right_rest_value), y,
            FieldRing.merge_sound(~F, ~field, values, G.Times{left_index, left_rest}, right_rest)),
          FieldRing.mul_swap(~F, ~field, y, left_value, right_rest_value)))

def FieldRing.insert_sound_at(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +coefficient: Nat, +monomial: G.Ring.Monomial,
  +other_coefficient: Nat, +other_monomial: G.Ring.Monomial, +rest: G.Ring.Poly,
  order: Cmp, +order_is: {G.Ring.compare(monomial, other_monomial) == order : Cmp},
  rest_sound: A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(coefficient, monomial, rest)),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial)), FieldRing.eval_poly(~F, ~field, values, rest)))) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.choose_poly(order,
      G.Term{coefficient, monomial, G.Term{other_coefficient, other_monomial, rest}},
      G.Term{Nat.add(coefficient, other_coefficient), other_monomial, rest},
      G.Term{other_coefficient, other_monomial, G.Ring.insert(coefficient, monomial, rest)})),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial)),
      A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, other_coefficient), FieldRing.eval_monomial(~F, ~field, values, other_monomial)), FieldRing.eval_poly(~F, ~field, values, rest)))):
  match order:
    case LT{}:
      A.Algebra.same_reflexive(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Term{coefficient, monomial, G.Term{other_coefficient, other_monomial, rest}}))
    case EQ{}:
      +c: F = FieldRing.of_nat(~F, ~field, coefficient)
      +d: F = FieldRing.of_nat(~F, ~field, other_coefficient)
      +other_value: F = FieldRing.eval_monomial(~F, ~field, values, other_monomial)
      +rest_value: F = FieldRing.eval_poly(~F, ~field, values, rest)
      +same: {other_monomial == monomial : G.Ring.Monomial} =
        Equal.sym(G.Ring.Monomial, monomial, other_monomial, G.Ring.compare_equal(monomial, other_monomial, order_is))
      %same : A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(coefficient, other_coefficient)), other_value), rest_value),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, FieldRing.eval_monomial(~F, ~field, values, _)), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, d, other_value), rest_value)))
      A.Algebra.same_transitive(~F, ~field,
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(coefficient, other_coefficient)), other_value), rest_value),
        A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, other_value), A.Algebra.mul(~F, ~field, d, other_value)), rest_value),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, other_value), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, d, other_value), rest_value)),
        A.Algebra.add_respects_left(~F, ~field,
          A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(coefficient, other_coefficient)), other_value),
          A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, other_value), A.Algebra.mul(~F, ~field, d, other_value)), rest_value,
          A.Algebra.same_transitive(~F, ~field,
            A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(coefficient, other_coefficient)), other_value),
            A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, c, d), other_value),
            A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, c, other_value), A.Algebra.mul(~F, ~field, d, other_value)),
            A.Algebra.mul_respects_left(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.add(coefficient, other_coefficient)), A.Algebra.add(~F, ~field, c, d), other_value,
              FieldRing.of_nat_add(~F, ~field, coefficient, other_coefficient)),
            A.Algebra.distributes_right(~F, ~field, c, d, other_value))),
        A.Algebra.add_associates(~F, ~field, A.Algebra.mul(~F, ~field, c, other_value), A.Algebra.mul(~F, ~field, d, other_value), rest_value))
    case GT{}:
      +term: F = A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial))
      +other_term: F = A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, other_coefficient), FieldRing.eval_monomial(~F, ~field, values, other_monomial))
      +rest_value: F = FieldRing.eval_poly(~F, ~field, values, rest)
      A.Algebra.same_transitive(~F, ~field,
        A.Algebra.add(~F, ~field, other_term, FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(coefficient, monomial, rest))),
        A.Algebra.add(~F, ~field, other_term, A.Algebra.add(~F, ~field, term, rest_value)),
        A.Algebra.add(~F, ~field, term, A.Algebra.add(~F, ~field, other_term, rest_value)),
        A.Algebra.add_respects_right(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(coefficient, monomial, rest)), A.Algebra.add(~F, ~field, term, rest_value), other_term, rest_sound),
        FieldRing.add_swap(~F, ~field, other_term, term, rest_value))

def FieldRing.insert_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +coefficient: Nat, +monomial: G.Ring.Monomial, +poly: G.Ring.Poly) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(coefficient, monomial, poly)),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial)), FieldRing.eval_poly(~F, ~field, values, poly))):
  match coefficient:
    case 0n:
      +value: F = FieldRing.eval_monomial(~F, ~field, values, monomial)
      +poly_value: F = FieldRing.eval_poly(~F, ~field, values, poly)
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), value), poly_value), poly_value,
        A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), value), poly_value), A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), poly_value), poly_value,
          A.Algebra.add_respects_left(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), value), A.Algebra.zero(~F, ~field), poly_value, A.Algebra.zero_mul(~F, ~field, value)),
          A.Algebra.zero_add(~F, ~field, poly_value)))
    case 1n+previous:
      match poly:
        case G.NoTerms{}:
          A.Algebra.same_reflexive(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Term{1n+previous, monomial, G.NoTerms{}}))
        case G.Term{+other_coefficient, +other_monomial, +rest}:
          FieldRing.insert_sound_at(~F, ~field, values, 1n+previous, monomial, other_coefficient, other_monomial, rest,
            G.Ring.compare(monomial, other_monomial), {==},
            FieldRing.insert_sound(~F, ~field, values, 1n+previous, monomial, rest))

def FieldRing.add_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +left: G.Ring.Poly, +right: G.Ring.Poly) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.add(left, right)), A.Algebra.add(~F, ~field, FieldRing.eval_poly(~F, ~field, values, left), FieldRing.eval_poly(~F, ~field, values, right))):
  match left:
    case G.NoTerms{}:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), FieldRing.eval_poly(~F, ~field, values, right)), FieldRing.eval_poly(~F, ~field, values, right),
        A.Algebra.zero_add(~F, ~field, FieldRing.eval_poly(~F, ~field, values, right)))
    case G.Term{+coefficient, +monomial, +rest}:
      +term: F = A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial))
      +rest_value: F = FieldRing.eval_poly(~F, ~field, values, rest)
      +right_value: F = FieldRing.eval_poly(~F, ~field, values, right)
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(coefficient, monomial, G.Ring.add(rest, right))),
        A.Algebra.add(~F, ~field, term, A.Algebra.add(~F, ~field, rest_value, right_value)),
        A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, term, rest_value), right_value),
        A.Algebra.same_transitive(~F, ~field,
          FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(coefficient, monomial, G.Ring.add(rest, right))),
          A.Algebra.add(~F, ~field, term, FieldRing.eval_poly(~F, ~field, values, G.Ring.add(rest, right))),
          A.Algebra.add(~F, ~field, term, A.Algebra.add(~F, ~field, rest_value, right_value)),
          FieldRing.insert_sound(~F, ~field, values, coefficient, monomial, G.Ring.add(rest, right)),
          A.Algebra.add_respects_right(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.add(rest, right)), A.Algebra.add(~F, ~field, rest_value, right_value), term,
            FieldRing.add_sound(~F, ~field, values, rest, right))),
        A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, term, rest_value), right_value), A.Algebra.add(~F, ~field, term, A.Algebra.add(~F, ~field, rest_value, right_value)),
          A.Algebra.add_associates(~F, ~field, term, rest_value, right_value)))

def FieldRing.scale_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +coefficient: Nat, +monomial: G.Ring.Monomial, +poly: G.Ring.Poly) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.scale(coefficient, monomial, poly)),
    A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial)), FieldRing.eval_poly(~F, ~field, values, poly))):
  match poly:
    case G.NoTerms{}:
      +factor: F = A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial))
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, factor, A.Algebra.zero(~F, ~field)), A.Algebra.zero(~F, ~field), A.Algebra.mul_zero(~F, ~field, factor))
    case G.Term{+other_coefficient, +other_monomial, +rest}:
      +c: F = FieldRing.of_nat(~F, ~field, coefficient)
      +d: F = FieldRing.of_nat(~F, ~field, other_coefficient)
      +value: F = FieldRing.eval_monomial(~F, ~field, values, monomial)
      +other_value: F = FieldRing.eval_monomial(~F, ~field, values, other_monomial)
      +rest_value: F = FieldRing.eval_poly(~F, ~field, values, rest)
      +factor: F = A.Algebra.mul(~F, ~field, c, value)
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(Nat.mul(coefficient, other_coefficient), G.Ring.merge(monomial, other_monomial),
          G.Ring.scale(coefficient, monomial, rest))),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.mul(coefficient, other_coefficient)), FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(monomial, other_monomial))),
          FieldRing.eval_poly(~F, ~field, values, G.Ring.scale(coefficient, monomial, rest))),
        A.Algebra.mul(~F, ~field, factor, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, d, other_value), rest_value)),
        FieldRing.insert_sound(~F, ~field, values, Nat.mul(coefficient, other_coefficient), G.Ring.merge(monomial, other_monomial),
          G.Ring.scale(coefficient, monomial, rest)),
        A.Algebra.same_transitive(~F, ~field,
          A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.mul(coefficient, other_coefficient)), FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(monomial, other_monomial))),
            FieldRing.eval_poly(~F, ~field, values, G.Ring.scale(coefficient, monomial, rest))),
          A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, A.Algebra.mul(~F, ~field, d, other_value)), A.Algebra.mul(~F, ~field, factor, rest_value)),
          A.Algebra.mul(~F, ~field, factor, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, d, other_value), rest_value)),
          A.Algebra.add_respects(~F, ~field,
            A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.mul(coefficient, other_coefficient)), FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(monomial, other_monomial))),
            A.Algebra.mul(~F, ~field, factor, A.Algebra.mul(~F, ~field, d, other_value)),
            FieldRing.eval_poly(~F, ~field, values, G.Ring.scale(coefficient, monomial, rest)),
            A.Algebra.mul(~F, ~field, factor, rest_value),
            A.Algebra.same_transitive(~F, ~field,
              A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, Nat.mul(coefficient, other_coefficient)), FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(monomial, other_monomial))),
              A.Algebra.mul(~F, ~field, A.Algebra.mul(~F, ~field, c, d), A.Algebra.mul(~F, ~field, value, other_value)),
              A.Algebra.mul(~F, ~field, factor, A.Algebra.mul(~F, ~field, d, other_value)),
              A.Algebra.mul_respects(~F, ~field,
                FieldRing.of_nat(~F, ~field, Nat.mul(coefficient, other_coefficient)), A.Algebra.mul(~F, ~field, c, d),
                FieldRing.eval_monomial(~F, ~field, values, G.Ring.merge(monomial, other_monomial)), A.Algebra.mul(~F, ~field, value, other_value),
                FieldRing.of_nat_mul(~F, ~field, coefficient, other_coefficient),
                FieldRing.merge_sound(~F, ~field, values, monomial, other_monomial)),
              FieldRing.mul_four(~F, ~field, c, d, value, other_value)),
            FieldRing.scale_sound(~F, ~field, values, coefficient, monomial, rest)),
          A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, factor, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, d, other_value), rest_value)), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, A.Algebra.mul(~F, ~field, d, other_value)), A.Algebra.mul(~F, ~field, factor, rest_value)),
            A.Algebra.distributes_left(~F, ~field, factor, A.Algebra.mul(~F, ~field, d, other_value), rest_value))))

def FieldRing.mul_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +left: G.Ring.Poly, +right: G.Ring.Poly) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(left, right)), A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, left), FieldRing.eval_poly(~F, ~field, values, right))):
  match left:
    case G.NoTerms{}:
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.zero(~F, ~field), FieldRing.eval_poly(~F, ~field, values, right)), A.Algebra.zero(~F, ~field), A.Algebra.zero_mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, right)))
    case G.Term{+coefficient, +monomial, +rest}:
      +factor: F = A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, coefficient), FieldRing.eval_monomial(~F, ~field, values, monomial))
      +rest_value: F = FieldRing.eval_poly(~F, ~field, values, rest)
      +right_value: F = FieldRing.eval_poly(~F, ~field, values, right)
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.add(G.Ring.scale(coefficient, monomial, right), G.Ring.mul(rest, right))),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, right_value), A.Algebra.mul(~F, ~field, rest_value, right_value)),
        A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, factor, rest_value), right_value),
        A.Algebra.same_transitive(~F, ~field,
          FieldRing.eval_poly(~F, ~field, values, G.Ring.add(G.Ring.scale(coefficient, monomial, right), G.Ring.mul(rest, right))),
          A.Algebra.add(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.scale(coefficient, monomial, right)), FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(rest, right))),
          A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, right_value), A.Algebra.mul(~F, ~field, rest_value, right_value)),
          FieldRing.add_sound(~F, ~field, values, G.Ring.scale(coefficient, monomial, right), G.Ring.mul(rest, right)),
          A.Algebra.add_respects(~F, ~field,
            FieldRing.eval_poly(~F, ~field, values, G.Ring.scale(coefficient, monomial, right)), A.Algebra.mul(~F, ~field, factor, right_value),
            FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(rest, right)), A.Algebra.mul(~F, ~field, rest_value, right_value),
            FieldRing.scale_sound(~F, ~field, values, coefficient, monomial, right),
            FieldRing.mul_sound(~F, ~field, values, rest, right))),
        A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, factor, rest_value), right_value), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, factor, right_value), A.Algebra.mul(~F, ~field, rest_value, right_value)),
          A.Algebra.distributes_right(~F, ~field, factor, rest_value, right_value)))

def FieldRing.of_nat_one(~F: Kind(&2), ~field: K.Field<F>) -> A.Algebra.Same(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field)):
  A.Algebra.add_zero(~F, ~field, A.Algebra.one(~F, ~field))

def FieldRing.unit_term(~F: Kind(&2), ~field: K.Field<F>, +value: F) -> A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), A.Algebra.zero(~F, ~field)), value):
  A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), value,
    A.Algebra.add_zero(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field)))),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), value,
      A.Algebra.mul_respects_left(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field)), FieldRing.of_nat_one(~F, ~field)),
      A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field)), value,
        A.Algebra.one_mul(~F, ~field, A.Algebra.mul(~F, ~field, value, A.Algebra.one(~F, ~field))), A.Algebra.mul_one(~F, ~field, value))))

def FieldRing.constant_term(~F: Kind(&2), ~field: K.Field<F>, +value: Nat) -> A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, value), A.Algebra.one(~F, ~field)), A.Algebra.zero(~F, ~field)), FieldRing.of_nat(~F, ~field, value)):
  A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, value), A.Algebra.one(~F, ~field)), A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, value), A.Algebra.one(~F, ~field)), FieldRing.of_nat(~F, ~field, value),
    A.Algebra.add_zero(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, value), A.Algebra.one(~F, ~field))), A.Algebra.mul_one(~F, ~field, FieldRing.of_nat(~F, ~field, value)))

def FieldRing.norm_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +expr: G.Ring.Expr) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(expr)), FieldRing.eval(~F, ~field, values, expr)):
  match expr:
    case G.Atom{+index}:
      FieldRing.unit_term(~F, ~field, FieldRing.lookup(~F, ~field, values, index))
    case G.Constant{+value}:
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(value, G.One{}, G.NoTerms{})),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, value), A.Algebra.one(~F, ~field)), A.Algebra.zero(~F, ~field)),
        FieldRing.of_nat(~F, ~field, value),
        FieldRing.insert_sound(~F, ~field, values, value, G.One{}, G.NoTerms{}),
        FieldRing.constant_term(~F, ~field, value))
    case G.Next{+body}:
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.insert(1n, G.One{}, G.Ring.norm(body))),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field)), FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(body))),
        A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), FieldRing.eval(~F, ~field, values, body)),
        FieldRing.insert_sound(~F, ~field, values, 1n, G.One{}, G.Ring.norm(body)),
        A.Algebra.add_respects(~F, ~field,
          A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field)), A.Algebra.one(~F, ~field),
          FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(body)), FieldRing.eval(~F, ~field, values, body),
          A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field)), FieldRing.of_nat(~F, ~field, 1n), A.Algebra.one(~F, ~field),
            A.Algebra.mul_one(~F, ~field, FieldRing.of_nat(~F, ~field, 1n)), FieldRing.of_nat_one(~F, ~field)),
          FieldRing.norm_sound(~F, ~field, values, body)))
    case G.Sum{+left, +right}:
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.add(G.Ring.norm(left), G.Ring.norm(right))),
        A.Algebra.add(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(right))),
        A.Algebra.add(~F, ~field, FieldRing.eval(~F, ~field, values, left), FieldRing.eval(~F, ~field, values, right)),
        FieldRing.add_sound(~F, ~field, values, G.Ring.norm(left), G.Ring.norm(right)),
        A.Algebra.add_respects(~F, ~field,
          FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval(~F, ~field, values, left),
          FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(right)), FieldRing.eval(~F, ~field, values, right),
          FieldRing.norm_sound(~F, ~field, values, left), FieldRing.norm_sound(~F, ~field, values, right)))
    case G.Product{+left, +right}:
      A.Algebra.same_transitive(~F, ~field,
        FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(G.Ring.norm(left), G.Ring.norm(right))),
        A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(right))),
        A.Algebra.mul(~F, ~field, FieldRing.eval(~F, ~field, values, left), FieldRing.eval(~F, ~field, values, right)),
        FieldRing.mul_sound(~F, ~field, values, G.Ring.norm(left), G.Ring.norm(right)),
        A.Algebra.mul_respects(~F, ~field,
          FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval(~F, ~field, values, left),
          FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(right)), FieldRing.eval(~F, ~field, values, right),
          FieldRing.norm_sound(~F, ~field, values, left), FieldRing.norm_sound(~F, ~field, values, right)))

def FieldRing.norm_sound_at(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +left: G.Ring.Expr, +right: G.Ring.Expr,
  same: {G.Ring.norm(right) == G.Ring.norm(left) : G.Ring.Poly}) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval(~F, ~field, values, right)):
  %same : A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, _), FieldRing.eval(~F, ~field, values, right))
  FieldRing.norm_sound(~F, ~field, values, right)

def FieldRing.semiring_equal(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +left: G.Ring.Expr, +right: G.Ring.Expr,
  same: {G.Ring.norm(left) == G.Ring.norm(right) : G.Ring.Poly}) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval(~F, ~field, values, left), FieldRing.eval(~F, ~field, values, right)):
  A.Algebra.same_transitive(~F, ~field, FieldRing.eval(~F, ~field, values, left), FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval(~F, ~field, values, right),
    A.Algebra.same_symmetric(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(left)), FieldRing.eval(~F, ~field, values, left), FieldRing.norm_sound(~F, ~field, values, left)),
    FieldRing.norm_sound_at(~F, ~field, values, left, right, Equal.sym(G.Ring.Poly, G.Ring.norm(left), G.Ring.norm(right), same)))

type FieldRing.Expr is Data:
  Variable{index: Nat}
  Number{value: Nat}
  Plus{left: FieldRing.Expr, right: FieldRing.Expr}
  Multiply{left: FieldRing.Expr, right: FieldRing.Expr}
  Negate{body: FieldRing.Expr}

type FieldRing.Split is Data:
  Split{positive: G.Ring.Poly, negative: G.Ring.Poly}

def FieldRing.positive(split: FieldRing.Split) -> G.Ring.Poly:
  match split:
    case Split{positive, negative}:
      positive

def FieldRing.negative(split: FieldRing.Split) -> G.Ring.Poly:
  match split:
    case Split{positive, negative}:
      negative

def FieldRing.split_plus(+left: FieldRing.Split, +right: FieldRing.Split) -> FieldRing.Split:
  Split{G.Ring.add(FieldRing.positive(left), FieldRing.positive(right)), G.Ring.add(FieldRing.negative(left), FieldRing.negative(right))}

def FieldRing.split_multiply(+left: FieldRing.Split, +right: FieldRing.Split) -> FieldRing.Split:
  Split{
    G.Ring.add(G.Ring.mul(FieldRing.positive(left), FieldRing.positive(right)), G.Ring.mul(FieldRing.negative(left), FieldRing.negative(right))),
    G.Ring.add(G.Ring.mul(FieldRing.positive(left), FieldRing.negative(right)), G.Ring.mul(FieldRing.negative(left), FieldRing.positive(right)))
  }

def FieldRing.split_negate(+body: FieldRing.Split) -> FieldRing.Split:
  Split{FieldRing.negative(body), FieldRing.positive(body)}

def FieldRing.split(expr: FieldRing.Expr) -> FieldRing.Split:
  match expr:
    case Variable{index}:
      Split{G.Ring.norm(G.Atom{index}), G.NoTerms{}}
    case Number{value}:
      Split{G.Ring.norm(G.Constant{value}), G.NoTerms{}}
    case Plus{left, right}:
      FieldRing.split_plus(FieldRing.split(left), FieldRing.split(right))
    case Multiply{left, right}:
      FieldRing.split_multiply(FieldRing.split(left), FieldRing.split(right))
    case Negate{body}:
      FieldRing.split_negate(FieldRing.split(body))

def FieldRing.value(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, expr: FieldRing.Expr) -> F:
  match expr:
    case Variable{index}:
      FieldRing.lookup(~F, ~field, values, index)
    case Number{value}:
      FieldRing.of_nat(~F, ~field, value)
    case Plus{left, right}:
      A.Algebra.add(~F, ~field, FieldRing.value(~F, ~field, values, left), FieldRing.value(~F, ~field, values, right))
    case Multiply{left, right}:
      A.Algebra.mul(~F, ~field, FieldRing.value(~F, ~field, values, left), FieldRing.value(~F, ~field, values, right))
    case Negate{body}:
      A.Algebra.neg(~F, ~field, FieldRing.value(~F, ~field, values, body))

def FieldRing.four(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, +d: F) -> FieldRing.Values<F>:
  Value{a, Value{b, Value{c, Value{d, NoValues{}}}}}

def FieldRing.product_pair_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +a: G.Ring.Poly, +b: G.Ring.Poly, +c: G.Ring.Poly, +d: G.Ring.Poly) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.add(G.Ring.mul(a, b), G.Ring.mul(c, d))),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, a), FieldRing.eval_poly(~F, ~field, values, b)), A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, c), FieldRing.eval_poly(~F, ~field, values, d)))):
  A.Algebra.same_transitive(~F, ~field,
    FieldRing.eval_poly(~F, ~field, values, G.Ring.add(G.Ring.mul(a, b), G.Ring.mul(c, d))),
    A.Algebra.add(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(a, b)), FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(c, d))),
    A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, a), FieldRing.eval_poly(~F, ~field, values, b)), A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, c), FieldRing.eval_poly(~F, ~field, values, d))),
    FieldRing.add_sound(~F, ~field, values, G.Ring.mul(a, b), G.Ring.mul(c, d)),
    A.Algebra.add_respects(~F, ~field,
      FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(a, b)), A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, a), FieldRing.eval_poly(~F, ~field, values, b)),
      FieldRing.eval_poly(~F, ~field, values, G.Ring.mul(c, d)), A.Algebra.mul(~F, ~field, FieldRing.eval_poly(~F, ~field, values, c), FieldRing.eval_poly(~F, ~field, values, d)),
      FieldRing.mul_sound(~F, ~field, values, a, b), FieldRing.mul_sound(~F, ~field, values, c, d)))

def FieldRing.split_sound(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +expr: FieldRing.Expr) ->
  A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, FieldRing.value(~F, ~field, values, expr), FieldRing.eval_poly(~F, ~field, values, FieldRing.negative(FieldRing.split(expr)))),
    FieldRing.eval_poly(~F, ~field, values, FieldRing.positive(FieldRing.split(expr)))):
  match expr:
    case Variable{+index}:
      +x: F = FieldRing.lookup(~F, ~field, values, index)
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, x, A.Algebra.zero(~F, ~field)), x, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(G.Atom{index})),
        A.Algebra.add_zero(~F, ~field, x),
        A.Algebra.same_symmetric(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(G.Atom{index})), x, FieldRing.norm_sound(~F, ~field, values, G.Atom{index})))
    case Number{+value}:
      +x: F = FieldRing.of_nat(~F, ~field, value)
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, x, A.Algebra.zero(~F, ~field)), x, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(G.Constant{value})),
        A.Algebra.add_zero(~F, ~field, x),
        A.Algebra.same_symmetric(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.norm(G.Constant{value})), x, FieldRing.norm_sound(~F, ~field, values, G.Constant{value})))
    case Negate{+body}:
      +e: F = FieldRing.value(~F, ~field, values, body)
      +p: F = FieldRing.eval_poly(~F, ~field, values, FieldRing.positive(FieldRing.split(body)))
      +n: F = FieldRing.eval_poly(~F, ~field, values, FieldRing.negative(FieldRing.split(body)))
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), p), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), A.Algebra.add(~F, ~field, e, n)), n,
        A.Algebra.add_respects_right(~F, ~field, p, A.Algebra.add(~F, ~field, e, n), A.Algebra.neg(~F, ~field, e), A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, e, n), p, FieldRing.split_sound(~F, ~field, values, body))),
        A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), A.Algebra.add(~F, ~field, e, n)), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), e), n), n,
          A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), e), n), A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), A.Algebra.add(~F, ~field, e, n)), A.Algebra.add_associates(~F, ~field, A.Algebra.neg(~F, ~field, e), e, n)),
          A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), e), n), A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), n), n,
            A.Algebra.add_respects_left(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.neg(~F, ~field, e), e), A.Algebra.zero(~F, ~field), n, A.Algebra.neg_add(~F, ~field, e)),
            A.Algebra.zero_add(~F, ~field, n))))
    case Plus{+left, +right}:
      +l: F = FieldRing.value(~F, ~field, values, left)
      +r: F = FieldRing.value(~F, ~field, values, right)
      +pl: F = FieldRing.eval_poly(~F, ~field, values, FieldRing.positive(FieldRing.split(left)))
      +nl: F = FieldRing.eval_poly(~F, ~field, values, FieldRing.negative(FieldRing.split(left)))
      +pr: F = FieldRing.eval_poly(~F, ~field, values, FieldRing.positive(FieldRing.split(right)))
      +nr: F = FieldRing.eval_poly(~F, ~field, values, FieldRing.negative(FieldRing.split(right)))
      A.Algebra.same_transitive(~F, ~field,
        A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, r), FieldRing.eval_poly(~F, ~field, values, G.Ring.add(FieldRing.negative(FieldRing.split(left)), FieldRing.negative(FieldRing.split(right))))),
        A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, nl), A.Algebra.add(~F, ~field, r, nr)),
        FieldRing.eval_poly(~F, ~field, values, G.Ring.add(FieldRing.positive(FieldRing.split(left)), FieldRing.positive(FieldRing.split(right)))),
        A.Algebra.same_transitive(~F, ~field,
          A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, r), FieldRing.eval_poly(~F, ~field, values, G.Ring.add(FieldRing.negative(FieldRing.split(left)), FieldRing.negative(FieldRing.split(right))))),
          A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, r), A.Algebra.add(~F, ~field, nl, nr)),
          A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, nl), A.Algebra.add(~F, ~field, r, nr)),
          A.Algebra.add_respects_right(~F, ~field,
            FieldRing.eval_poly(~F, ~field, values, G.Ring.add(FieldRing.negative(FieldRing.split(left)), FieldRing.negative(FieldRing.split(right)))),
            A.Algebra.add(~F, ~field, nl, nr), A.Algebra.add(~F, ~field, l, r),
            FieldRing.add_sound(~F, ~field, values, FieldRing.negative(FieldRing.split(left)), FieldRing.negative(FieldRing.split(right)))),
          FieldRing.semiring_equal(~F, ~field, FieldRing.four(~F, ~field, l, r, nl, nr),
            G.Sum{G.Sum{G.Atom{0n}, G.Atom{1n}}, G.Sum{G.Atom{2n}, G.Atom{3n}}},
            G.Sum{G.Sum{G.Atom{0n}, G.Atom{2n}}, G.Sum{G.Atom{1n}, G.Atom{3n}}}, {==})),
        A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, nl), A.Algebra.add(~F, ~field, r, nr)), A.Algebra.add(~F, ~field, pl, pr),
          FieldRing.eval_poly(~F, ~field, values, G.Ring.add(FieldRing.positive(FieldRing.split(left)), FieldRing.positive(FieldRing.split(right)))),
          A.Algebra.add_respects(~F, ~field, A.Algebra.add(~F, ~field, l, nl), pl, A.Algebra.add(~F, ~field, r, nr), pr, FieldRing.split_sound(~F, ~field, values, left), FieldRing.split_sound(~F, ~field, values, right)),
          A.Algebra.same_symmetric(~F, ~field,
            FieldRing.eval_poly(~F, ~field, values, G.Ring.add(FieldRing.positive(FieldRing.split(left)), FieldRing.positive(FieldRing.split(right)))),
            A.Algebra.add(~F, ~field, pl, pr),
            FieldRing.add_sound(~F, ~field, values, FieldRing.positive(FieldRing.split(left)), FieldRing.positive(FieldRing.split(right))))))
    case Multiply{+left, +right}:
      +l: F = FieldRing.value(~F, ~field, values, left)
      +r: F = FieldRing.value(~F, ~field, values, right)
      +positive_left: G.Ring.Poly = FieldRing.positive(FieldRing.split(left))
      +negative_left: G.Ring.Poly = FieldRing.negative(FieldRing.split(left))
      +positive_right: G.Ring.Poly = FieldRing.positive(FieldRing.split(right))
      +negative_right: G.Ring.Poly = FieldRing.negative(FieldRing.split(right))
      +pl: F = FieldRing.eval_poly(~F, ~field, values, positive_left)
      +nl: F = FieldRing.eval_poly(~F, ~field, values, negative_left)
      +pr: F = FieldRing.eval_poly(~F, ~field, values, positive_right)
      +nr: F = FieldRing.eval_poly(~F, ~field, values, negative_right)
      +cross: G.Ring.Poly = G.Ring.add(G.Ring.mul(positive_left, negative_right), G.Ring.mul(negative_left, positive_right))
      +direct: G.Ring.Poly = G.Ring.add(G.Ring.mul(positive_left, positive_right), G.Ring.mul(negative_left, negative_right))
      +expanded: F = A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, l, r), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, l, nl), nr), A.Algebra.mul(~F, ~field, nl, A.Algebra.add(~F, ~field, r, nr))))
      +grouped: F = A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, l, nl), A.Algebra.add(~F, ~field, r, nr)), A.Algebra.mul(~F, ~field, nl, nr))
      A.Algebra.same_transitive(~F, ~field,
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, l, r), FieldRing.eval_poly(~F, ~field, values, cross)),
        A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, l, r), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, pl, nr), A.Algebra.mul(~F, ~field, nl, pr))),
        FieldRing.eval_poly(~F, ~field, values, direct),
        A.Algebra.add_respects_right(~F, ~field, FieldRing.eval_poly(~F, ~field, values, cross), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, pl, nr), A.Algebra.mul(~F, ~field, nl, pr)), A.Algebra.mul(~F, ~field, l, r),
          FieldRing.product_pair_sound(~F, ~field, values, positive_left, negative_right, negative_left, positive_right)),
        A.Algebra.same_transitive(~F, ~field,
          A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, l, r), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, pl, nr), A.Algebra.mul(~F, ~field, nl, pr))), expanded, FieldRing.eval_poly(~F, ~field, values, direct),
          A.Algebra.add_respects_right(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, pl, nr), A.Algebra.mul(~F, ~field, nl, pr)), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, l, nl), nr), A.Algebra.mul(~F, ~field, nl, A.Algebra.add(~F, ~field, r, nr))), A.Algebra.mul(~F, ~field, l, r),
            A.Algebra.add_respects(~F, ~field, A.Algebra.mul(~F, ~field, pl, nr), A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, l, nl), nr), A.Algebra.mul(~F, ~field, nl, pr), A.Algebra.mul(~F, ~field, nl, A.Algebra.add(~F, ~field, r, nr)),
              A.Algebra.mul_respects_left(~F, ~field, pl, A.Algebra.add(~F, ~field, l, nl), nr, A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, l, nl), pl, FieldRing.split_sound(~F, ~field, values, left))),
              A.Algebra.mul_respects_right(~F, ~field, pr, A.Algebra.add(~F, ~field, r, nr), nl, A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, r, nr), pr, FieldRing.split_sound(~F, ~field, values, right))))),
          A.Algebra.same_transitive(~F, ~field, expanded, grouped, FieldRing.eval_poly(~F, ~field, values, direct),
            FieldRing.semiring_equal(~F, ~field, FieldRing.four(~F, ~field, l, r, nl, nr),
              G.Sum{G.Product{G.Atom{0n}, G.Atom{1n}}, G.Sum{G.Product{G.Sum{G.Atom{0n}, G.Atom{2n}}, G.Atom{3n}}, G.Product{G.Atom{2n}, G.Sum{G.Atom{1n}, G.Atom{3n}}}}},
              G.Sum{G.Product{G.Sum{G.Atom{0n}, G.Atom{2n}}, G.Sum{G.Atom{1n}, G.Atom{3n}}}, G.Product{G.Atom{2n}, G.Atom{3n}}}, {==}),
            A.Algebra.same_transitive(~F, ~field, grouped, A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, pl, pr), A.Algebra.mul(~F, ~field, nl, nr)), FieldRing.eval_poly(~F, ~field, values, direct),
              A.Algebra.add_respects_left(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, l, nl), A.Algebra.add(~F, ~field, r, nr)), A.Algebra.mul(~F, ~field, pl, pr), A.Algebra.mul(~F, ~field, nl, nr),
                A.Algebra.mul_respects(~F, ~field, A.Algebra.add(~F, ~field, l, nl), pl, A.Algebra.add(~F, ~field, r, nr), pr, FieldRing.split_sound(~F, ~field, values, left), FieldRing.split_sound(~F, ~field, values, right))),
              A.Algebra.same_symmetric(~F, ~field, FieldRing.eval_poly(~F, ~field, values, direct), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, pl, pr), A.Algebra.mul(~F, ~field, nl, nr)),
                FieldRing.product_pair_sound(~F, ~field, values, positive_left, positive_right, negative_left, negative_right))))))

def FieldRing.poly_same_at(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +poly: G.Ring.Poly, +other: G.Ring.Poly, +target: F,
  equal: {other == poly : G.Ring.Poly}, proof: A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, other), target)) ->
  A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, poly), target):
  %equal : A.Algebra.Same(~F, ~field, FieldRing.eval_poly(~F, ~field, values, _), target)
  proof

def FieldRing.add_cancel_right(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: A.Algebra.Same(~F, ~field, A.Algebra.add(~F, ~field, a, c), A.Algebra.add(~F, ~field, b, c))) -> A.Algebra.Same(~F, ~field, a, b):
  A.Algebra.add_cancel_left(~F, ~field, c, a, b,
    A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, c, a), A.Algebra.add(~F, ~field, a, c), A.Algebra.add(~F, ~field, c, b), A.Algebra.add_commutes(~F, ~field, c, a),
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, a, c), A.Algebra.add(~F, ~field, b, c), A.Algebra.add(~F, ~field, c, b), same, A.Algebra.add_commutes(~F, ~field, b, c))))

def FieldRing.three(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> FieldRing.Values<F>:
  Value{a, Value{b, Value{c, NoValues{}}}}

def FieldRing.equal(~F: Kind(&2), ~field: K.Field<F>, +values: FieldRing.Values<F>, +left: FieldRing.Expr, +right: FieldRing.Expr,
  same: {G.Ring.add(FieldRing.positive(FieldRing.split(left)), FieldRing.negative(FieldRing.split(right))) ==
    G.Ring.add(FieldRing.positive(FieldRing.split(right)), FieldRing.negative(FieldRing.split(left))) : G.Ring.Poly}) ->
  A.Algebra.Same(~F, ~field, FieldRing.value(~F, ~field, values, left), FieldRing.value(~F, ~field, values, right)):
  +l: F = FieldRing.value(~F, ~field, values, left)
  +r: F = FieldRing.value(~F, ~field, values, right)
  +positive_left: G.Ring.Poly = FieldRing.positive(FieldRing.split(left))
  +negative_left: G.Ring.Poly = FieldRing.negative(FieldRing.split(left))
  +positive_right: G.Ring.Poly = FieldRing.positive(FieldRing.split(right))
  +negative_right: G.Ring.Poly = FieldRing.negative(FieldRing.split(right))
  +pl: F = FieldRing.eval_poly(~F, ~field, values, positive_left)
  +nl: F = FieldRing.eval_poly(~F, ~field, values, negative_left)
  +pr: F = FieldRing.eval_poly(~F, ~field, values, positive_right)
  +nr: F = FieldRing.eval_poly(~F, ~field, values, negative_right)
  FieldRing.add_cancel_right(~F, ~field, l, r, A.Algebra.add(~F, ~field, nl, nr),
    A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, l, A.Algebra.add(~F, ~field, nl, nr)), A.Algebra.add(~F, ~field, pl, nr), A.Algebra.add(~F, ~field, r, A.Algebra.add(~F, ~field, nl, nr)),
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, l, A.Algebra.add(~F, ~field, nl, nr)), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, nl), nr), A.Algebra.add(~F, ~field, pl, nr),
        A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, l, nl), nr), A.Algebra.add(~F, ~field, l, A.Algebra.add(~F, ~field, nl, nr)), A.Algebra.add_associates(~F, ~field, l, nl, nr)),
        A.Algebra.add_respects_left(~F, ~field, A.Algebra.add(~F, ~field, l, nl), pl, nr, FieldRing.split_sound(~F, ~field, values, left))),
      A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, pl, nr), A.Algebra.add(~F, ~field, pr, nl), A.Algebra.add(~F, ~field, r, A.Algebra.add(~F, ~field, nl, nr)),
        A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, pl, nr), FieldRing.eval_poly(~F, ~field, values, G.Ring.add(positive_left, negative_right)), A.Algebra.add(~F, ~field, pr, nl),
          A.Algebra.same_symmetric(~F, ~field, FieldRing.eval_poly(~F, ~field, values, G.Ring.add(positive_left, negative_right)), A.Algebra.add(~F, ~field, pl, nr),
            FieldRing.add_sound(~F, ~field, values, positive_left, negative_right)),
          FieldRing.poly_same_at(~F, ~field, values, G.Ring.add(positive_left, negative_right), G.Ring.add(positive_right, negative_left), A.Algebra.add(~F, ~field, pr, nl),
            Equal.sym(G.Ring.Poly, G.Ring.add(positive_left, negative_right), G.Ring.add(positive_right, negative_left), same),
            FieldRing.add_sound(~F, ~field, values, positive_right, negative_left))),
        A.Algebra.same_transitive(~F, ~field, A.Algebra.add(~F, ~field, pr, nl), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, r, nr), nl), A.Algebra.add(~F, ~field, r, A.Algebra.add(~F, ~field, nl, nr)),
          A.Algebra.add_respects_left(~F, ~field, pr, A.Algebra.add(~F, ~field, r, nr), nl, A.Algebra.same_symmetric(~F, ~field, A.Algebra.add(~F, ~field, r, nr), pr, FieldRing.split_sound(~F, ~field, values, right))),
          FieldRing.semiring_equal(~F, ~field, FieldRing.three(~F, ~field, r, nr, nl),
            G.Sum{G.Sum{G.Atom{0n}, G.Atom{1n}}, G.Atom{2n}},
            G.Sum{G.Atom{0n}, G.Sum{G.Atom{2n}, G.Atom{1n}}}, {==})))))
