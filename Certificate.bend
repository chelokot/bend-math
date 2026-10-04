import Base
import ./Field.bend as K
import ./FieldAlgebra.bend as A
import ./FieldRing.bend as R
import ./FieldOrder.bend as O
import ./Ring.bend as G

type Certificate.Both<-L: Kind(&2), -M: Kind(&2)> is Data:
  Both{first: L, second: M}

type Certificate.Exprs is Data:
  NoExprs{}
  MoreExprs{head: R.FieldRing.Expr, tail: Certificate.Exprs}

type Certificate.Indices is Data:
  NoIndices{}
  MoreIndices{head: Nat, tail: Certificate.Indices}

type Certificate.Term is Data:
  Product{coefficient: Nat, factors: Certificate.Indices, square: R.FieldRing.Expr}
  Multiple{equation: Nat, multiplier: R.FieldRing.Expr}

type Certificate.Terms is Data:
  NoTerms{}
  MoreTerms{head: Certificate.Term, tail: Certificate.Terms}

def Certificate.nth(exprs: Certificate.Exprs, index: Nat) -> R.FieldRing.Expr:
  match exprs:
    case NoExprs{}:
      R.Number{0n}
    case MoreExprs{head, tail}:
      match index:
        case 0n:
          head
        case 1n+previous:
          Certificate.nth(tail, previous)

def Certificate.product(+exprs: Certificate.Exprs, factors: Certificate.Indices) -> R.FieldRing.Expr:
  match factors:
    case NoIndices{}:
      R.Number{1n}
    case MoreIndices{head, tail}:
      R.Multiply{Certificate.nth(exprs, head), Certificate.product(exprs, tail)}

def Certificate.term(+facts: Certificate.Exprs, +equations: Certificate.Exprs, term: Certificate.Term) -> R.FieldRing.Expr:
  match term:
    case Product{coefficient, factors, +square}:
      R.Multiply{R.Number{coefficient}, R.Multiply{Certificate.product(facts, factors), R.Multiply{square, square}}}
    case Multiple{equation, multiplier}:
      R.Multiply{multiplier, Certificate.nth(equations, equation)}

def Certificate.sum(+facts: Certificate.Exprs, +equations: Certificate.Exprs, terms: Certificate.Terms) -> R.FieldRing.Expr:
  match terms:
    case NoTerms{}:
      R.Number{0n}
    case MoreTerms{head, tail}:
      R.Plus{Certificate.term(facts, equations, head), Certificate.sum(facts, equations, tail)}

def Certificate.value(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>, expr: R.FieldRing.Expr) -> F:
  R.FieldRing.value(~F, ~field, values, expr)

def Certificate.Facts(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>, exprs: Certificate.Exprs) -> Kind(&2):
  match exprs:
    case NoExprs{}:
      Unit
    case MoreExprs{head, tail}:
      Certificate.Both<A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, head)), Certificate.Facts(~F, ~field, values, tail)>

def Certificate.Equations(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>, exprs: Certificate.Exprs) -> Kind(&2):
  match exprs:
    case NoExprs{}:
      Unit
    case MoreExprs{head, tail}:
      Certificate.Both<Certificate.Both<A.Algebra.le(~F, ~field, Certificate.value(~F, ~field, values, head), A.Algebra.zero(~F, ~field)), A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, head))>,
        Certificate.Equations(~F, ~field, values, tail)>

def Certificate.fact(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>, +exprs: Certificate.Exprs, +facts: Certificate.Facts(~F, ~field, values, exprs), +index: Nat) ->
  A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, Certificate.nth(exprs, index))):
  match exprs:
    case NoExprs{}:
      K.Field.le_reflexive(F, field)(A.Algebra.zero(~F, ~field))
    case MoreExprs{+head, +tail}:
      match facts:
        case Both{+first, +second}:
          match index:
            case 0n:
              first
            case 1n+previous:
              Certificate.fact(~F, ~field, values, tail, second, previous)

def Certificate.equation(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>, +exprs: Certificate.Exprs, +equations: Certificate.Equations(~F, ~field, values, exprs), +index: Nat) ->
  A.Algebra.Same(~F, ~field, Certificate.value(~F, ~field, values, Certificate.nth(exprs, index)), A.Algebra.zero(~F, ~field)):
  match exprs:
    case NoExprs{}:
      A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field))
    case MoreExprs{+head, +tail}:
      match equations:
        case Both{Both{+below, +above}, +second}:
          match index:
            case 0n:
              (below, above)
            case 1n+previous:
              Certificate.equation(~F, ~field, values, tail, second, previous)

def Certificate.square_order(~F: Kind(&2), ~field: K.Field<F>, +a: F, order: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), a), A.Algebra.le(~F, ~field, a, A.Algebra.zero(~F, ~field)))) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, a, a)):
  match order:
    case Inl{+nonnegative}:
      K.Field.mul_nonnegative(F, field)(a, a, nonnegative, nonnegative)
    case Inr{+nonpositive}:
      A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, a)), A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, a, a),
        K.Field.mul_nonnegative(F, field)(A.Algebra.neg(~F, ~field, a), A.Algebra.neg(~F, ~field, a),
          A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.neg(~F, ~field, a), A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, a), O.FieldOrder.le_negate(~F, ~field, a, A.Algebra.zero(~F, ~field), nonpositive),
            R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Negate{R.Number{0n}}, R.Number{0n}, {==}), A.Algebra.same_reflexive(~F, ~field, A.Algebra.neg(~F, ~field, a))),
          A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.neg(~F, ~field, a), A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, a), O.FieldOrder.le_negate(~F, ~field, a, A.Algebra.zero(~F, ~field), nonpositive),
            R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Negate{R.Number{0n}}, R.Number{0n}, {==}), A.Algebra.same_reflexive(~F, ~field, A.Algebra.neg(~F, ~field, a)))),
        A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field)),
        R.FieldRing.equal(~F, ~field, R.Value{a, R.NoValues{}},
          R.Multiply{R.Negate{R.Variable{0n}}, R.Negate{R.Variable{0n}}}, R.Multiply{R.Variable{0n}, R.Variable{0n}}, {==}))

def Certificate.square_nonnegative(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, a, a)):
  Certificate.square_order(~F, ~field, a, K.Field.le_total(F, field)(A.Algebra.zero(~F, ~field), a))

def Certificate.product_nonnegative(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>, +exprs: Certificate.Exprs, +facts: Certificate.Facts(~F, ~field, values, exprs),
  +factors: Certificate.Indices) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, Certificate.product(exprs, factors))):
  match factors:
    case NoIndices{}:
      O.FieldOrder.zero_le_of_nat(~F, ~field, 1n)
    case MoreIndices{+head, +tail}:
      K.Field.mul_nonnegative(F, field)(Certificate.value(~F, ~field, values, Certificate.nth(exprs, head)), Certificate.value(~F, ~field, values, Certificate.product(exprs, tail)),
        Certificate.fact(~F, ~field, values, exprs, facts, head), Certificate.product_nonnegative(~F, ~field, values, exprs, facts, tail))

def Certificate.term_nonnegative(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>,
  +facts: Certificate.Exprs, +fact_proofs: Certificate.Facts(~F, ~field, values, facts),
  +equations: Certificate.Exprs, +equation_proofs: Certificate.Equations(~F, ~field, values, equations),
  +term: Certificate.Term) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, Certificate.term(facts, equations, term))):
  match term:
    case Product{+coefficient, +factors, +square}:
      +product: F = Certificate.value(~F, ~field, values, Certificate.product(facts, factors))
      +root: F = Certificate.value(~F, ~field, values, square)
      K.Field.mul_nonnegative(F, field)(R.FieldRing.of_nat(~F, ~field, coefficient), A.Algebra.mul(~F, ~field, product, A.Algebra.mul(~F, ~field, root, root)),
        O.FieldOrder.zero_le_of_nat(~F, ~field, coefficient),
        K.Field.mul_nonnegative(F, field)(product, A.Algebra.mul(~F, ~field, root, root),
          Certificate.product_nonnegative(~F, ~field, values, facts, fact_proofs, factors),
          Certificate.square_nonnegative(~F, ~field, root)))
    case Multiple{+equation, +multiplier}:
      +factor: F = Certificate.value(~F, ~field, values, multiplier)
      +zero_value: F = Certificate.value(~F, ~field, values, Certificate.nth(equations, equation))
      O.FieldOrder.le_of_same(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, factor, zero_value),
        A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, factor, zero_value), A.Algebra.zero(~F, ~field),
          A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, factor, zero_value), A.Algebra.mul(~F, ~field, factor, A.Algebra.zero(~F, ~field)), A.Algebra.zero(~F, ~field),
            A.Algebra.mul_respects_right(~F, ~field, zero_value, A.Algebra.zero(~F, ~field), factor, Certificate.equation(~F, ~field, values, equations, equation_proofs, equation)),
            A.Algebra.mul_zero(~F, ~field, factor))))

def Certificate.sum_nonnegative(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>,
  +facts: Certificate.Exprs, +fact_proofs: Certificate.Facts(~F, ~field, values, facts),
  +equations: Certificate.Exprs, +equation_proofs: Certificate.Equations(~F, ~field, values, equations),
  +terms: Certificate.Terms) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, Certificate.sum(facts, equations, terms))):
  match terms:
    case NoTerms{}:
      K.Field.le_reflexive(F, field)(A.Algebra.zero(~F, ~field))
    case MoreTerms{+head, +tail}:
      +first: F = Certificate.value(~F, ~field, values, Certificate.term(facts, equations, head))
      +rest: F = Certificate.value(~F, ~field, values, Certificate.sum(facts, equations, tail))
      A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.zero(~F, ~field)), A.Algebra.add(~F, ~field, first, rest), A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, first, rest),
        O.FieldOrder.le_add_both(~F, ~field, A.Algebra.zero(~F, ~field), first, A.Algebra.zero(~F, ~field), rest,
          Certificate.term_nonnegative(~F, ~field, values, facts, fact_proofs, equations, equation_proofs, head),
          Certificate.sum_nonnegative(~F, ~field, values, facts, fact_proofs, equations, equation_proofs, tail)),
        A.Algebra.add_zero(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, first, rest)))

def Certificate.nonpositive_scaled(~F: Kind(&2), ~field: K.Field<F>, +k: F, +g: F, k_nonnegative: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), k), g_nonpositive: A.Algebra.le(~F, ~field, g, A.Algebra.zero(~F, ~field))) -> A.Algebra.le(~F, ~field, A.Algebra.mul(~F, ~field, k, g), A.Algebra.zero(~F, ~field)):
  +negated: F = A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, k, g))
  A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, negated), A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.mul(~F, ~field, k, g), A.Algebra.zero(~F, ~field),
    O.FieldOrder.le_negate(~F, ~field, A.Algebra.zero(~F, ~field), negated,
      A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, k, A.Algebra.neg(~F, ~field, g)), A.Algebra.zero(~F, ~field), negated,
        K.Field.mul_nonnegative(F, field)(k, A.Algebra.neg(~F, ~field, g), k_nonnegative,
          A.Algebra.le_respects(~F, ~field, A.Algebra.neg(~F, ~field, A.Algebra.zero(~F, ~field)), A.Algebra.neg(~F, ~field, g), A.Algebra.zero(~F, ~field), A.Algebra.neg(~F, ~field, g), O.FieldOrder.le_negate(~F, ~field, g, A.Algebra.zero(~F, ~field), g_nonpositive),
            R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Negate{R.Number{0n}}, R.Number{0n}, {==}), A.Algebra.same_reflexive(~F, ~field, A.Algebra.neg(~F, ~field, g)))),
        A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field)),
        R.FieldRing.equal(~F, ~field, R.Value{k, R.Value{g, R.NoValues{}}},
          R.Multiply{R.Variable{0n}, R.Negate{R.Variable{1n}}}, R.Negate{R.Multiply{R.Variable{0n}, R.Variable{1n}}}, {==}))),
    R.FieldRing.equal(~F, ~field, R.Value{k, R.Value{g, R.NoValues{}}},
      R.Negate{R.Negate{R.Multiply{R.Variable{0n}, R.Variable{1n}}}}, R.Multiply{R.Variable{0n}, R.Variable{1n}}, {==}),
    R.FieldRing.equal(~F, ~field, R.NoValues{}, R.Negate{R.Number{0n}}, R.Number{0n}, {==}))

def Certificate.scaled_order(~F: Kind(&2), ~field: K.Field<F>, +denominator: Nat, +g: F, +scaled: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n+denominator), g)),
  order: Or(A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), g), A.Algebra.le(~F, ~field, g, A.Algebra.zero(~F, ~field)))) -> A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), g):
  match order:
    case Inl{nonnegative}:
      nonnegative
    case Inr{+nonpositive}:
      +k: F = R.FieldRing.of_nat(~F, ~field, denominator)
      K.Field.le_transitive(F, field)(A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, g, A.Algebra.mul(~F, ~field, k, g)), g,
        A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), k), g), A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, g, A.Algebra.mul(~F, ~field, k, g)), scaled, A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field)),
          A.Algebra.same_transitive(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.one(~F, ~field), k), g), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), g), A.Algebra.mul(~F, ~field, k, g)), A.Algebra.add(~F, ~field, g, A.Algebra.mul(~F, ~field, k, g)),
            A.Algebra.distributes_right(~F, ~field, A.Algebra.one(~F, ~field), k, g),
            A.Algebra.add_respects_left(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.one(~F, ~field), g), g, A.Algebra.mul(~F, ~field, k, g), A.Algebra.one_mul(~F, ~field, g)))),
        A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, g, A.Algebra.mul(~F, ~field, k, g)), A.Algebra.add(~F, ~field, g, A.Algebra.zero(~F, ~field)), A.Algebra.add(~F, ~field, g, A.Algebra.mul(~F, ~field, k, g)), g,
          O.FieldOrder.le_add_left(~F, ~field, A.Algebra.mul(~F, ~field, k, g), A.Algebra.zero(~F, ~field), g,
            Certificate.nonpositive_scaled(~F, ~field, k, g, O.FieldOrder.zero_le_of_nat(~F, ~field, denominator), nonpositive)),
          A.Algebra.same_reflexive(~F, ~field, A.Algebra.add(~F, ~field, g, A.Algebra.mul(~F, ~field, k, g))), A.Algebra.add_zero(~F, ~field, g)))

def Certificate.Valid(+facts: Certificate.Exprs, +equations: Certificate.Exprs, +denominator: Nat, +goal: R.FieldRing.Expr, +terms: Certificate.Terms) -> Type:
  {G.Ring.add(R.FieldRing.positive(R.FieldRing.split(R.Multiply{R.Number{1n+denominator}, goal})),
      R.FieldRing.negative(R.FieldRing.split(Certificate.sum(facts, equations, terms)))) ==
    G.Ring.add(R.FieldRing.positive(R.FieldRing.split(Certificate.sum(facts, equations, terms))),
      R.FieldRing.negative(R.FieldRing.split(R.Multiply{R.Number{1n+denominator}, goal}))) : G.Ring.Poly}

def Certificate.nonnegative(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>,
  +facts: Certificate.Exprs, +fact_proofs: Certificate.Facts(~F, ~field, values, facts),
  +equations: Certificate.Exprs, +equation_proofs: Certificate.Equations(~F, ~field, values, equations),
  +denominator: Nat, +goal: R.FieldRing.Expr, +terms: Certificate.Terms,
  same: Certificate.Valid(facts, equations, denominator, goal, terms)) ->
  A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), Certificate.value(~F, ~field, values, goal)):
  +g: F = Certificate.value(~F, ~field, values, goal)
  +total: F = Certificate.value(~F, ~field, values, Certificate.sum(facts, equations, terms))
  Certificate.scaled_order(~F, ~field, denominator, g,
    A.Algebra.le_respects(~F, ~field, A.Algebra.zero(~F, ~field), total, A.Algebra.zero(~F, ~field), A.Algebra.mul(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n+denominator), g),
      Certificate.sum_nonnegative(~F, ~field, values, facts, fact_proofs, equations, equation_proofs, terms),
      A.Algebra.same_reflexive(~F, ~field, A.Algebra.zero(~F, ~field)),
      A.Algebra.same_symmetric(~F, ~field, A.Algebra.mul(~F, ~field, R.FieldRing.of_nat(~F, ~field, 1n+denominator), g), total,
        R.FieldRing.equal(~F, ~field, values, R.Multiply{R.Number{1n+denominator}, goal}, Certificate.sum(facts, equations, terms), same))),
    K.Field.le_total(F, field)(A.Algebra.zero(~F, ~field), g))

def Certificate.le(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>,
  +facts: Certificate.Exprs, +fact_proofs: Certificate.Facts(~F, ~field, values, facts),
  +equations: Certificate.Exprs, +equation_proofs: Certificate.Equations(~F, ~field, values, equations),
  +lower: R.FieldRing.Expr, +upper: R.FieldRing.Expr, +denominator: Nat, +terms: Certificate.Terms,
  same: Certificate.Valid(facts, equations, denominator, R.Plus{upper, R.Negate{lower}}, terms)) ->
  A.Algebra.le(~F, ~field, Certificate.value(~F, ~field, values, lower), Certificate.value(~F, ~field, values, upper)):
  +l: F = Certificate.value(~F, ~field, values, lower)
  +u: F = Certificate.value(~F, ~field, values, upper)
  A.Algebra.le_respects(~F, ~field, A.Algebra.add(~F, ~field, A.Algebra.zero(~F, ~field), l), A.Algebra.add(~F, ~field, A.Algebra.add(~F, ~field, u, A.Algebra.neg(~F, ~field, l)), l), l, u,
    K.Field.le_add(F, field)(A.Algebra.zero(~F, ~field), A.Algebra.add(~F, ~field, u, A.Algebra.neg(~F, ~field, l)), l,
      Certificate.nonnegative(~F, ~field, values, facts, fact_proofs, equations, equation_proofs, denominator, R.Plus{upper, R.Negate{lower}}, terms, same)),
    A.Algebra.zero_add(~F, ~field, l),
    R.FieldRing.equal(~F, ~field, R.Value{u, R.Value{l, R.NoValues{}}},
      R.Plus{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, R.Variable{1n}}, R.Variable{0n}, {==}))

def Certificate.same(~F: Kind(&2), ~field: K.Field<F>, +values: R.FieldRing.Values<F>,
  +equations: Certificate.Exprs, +equation_proofs: Certificate.Equations(~F, ~field, values, equations),
  +left: R.FieldRing.Expr, +right: R.FieldRing.Expr, +forward: Certificate.Terms, +backward: Certificate.Terms,
  forward_valid: Certificate.Valid(NoExprs{}, equations, 0n, R.Plus{right, R.Negate{left}}, forward),
  backward_valid: Certificate.Valid(NoExprs{}, equations, 0n, R.Plus{left, R.Negate{right}}, backward)) ->
  A.Algebra.Same(~F, ~field, Certificate.value(~F, ~field, values, left), Certificate.value(~F, ~field, values, right)):
  (
    Certificate.le(~F, ~field, values, NoExprs{}, Unit{}, equations, equation_proofs, left, right, 0n, forward, forward_valid),
    Certificate.le(~F, ~field, values, NoExprs{}, Unit{}, equations, equation_proofs, right, left, 0n, backward, backward_valid)
  )
