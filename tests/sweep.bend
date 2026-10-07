import Base
import ../Field.bend as K
import ../FieldAlgebra.bend as A
import ../FieldOrder.bend as O
import ../Sweep.bend as S

def negation_sweep(~F: Kind(&2), ~field: K.Field<F>, ~list: List<&2, F>, +pending: List<&2, F>, +a: F, +b: F, +order: A.Algebra.le(~F, ~field, a, b),
  +marked: S.Sweep.Marked(F, field, a, b, pending, list)) -> A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a)):
  match pending:
    case Nil{}:
      O.FieldOrder.le_negate(~F, ~field, a, b, order)
    case +split <> rest:
      S.Sweep.cases_of(~F, ~field, split, a, A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a)), K.Field.le_decidable(F, field)(split, a),
        +left => negation_sweep(~F, ~field, ~list, rest, a, b, order, S.Sweep.skip(~F, ~field, a, b, split, rest, list, Inl{left}, marked)),
        +inside_left => S.Sweep.cases_of(~F, ~field, b, split, A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a)), K.Field.le_decidable(F, field)(b, split),
          +right => negation_sweep(~F, ~field, ~list, rest, a, b, order, S.Sweep.skip(~F, ~field, a, b, split, rest, list, Inr{right}, marked)),
          +inside_right => K.Field.le_transitive(F, field)(A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, split), A.Algebra.neg(~F, ~field, a),
            negation_sweep(~F, ~field, ~list, rest, split, b, inside_right, S.Sweep.right(~F, ~field, a, b, split, rest, list, inside_left, marked)),
            negation_sweep(~F, ~field, ~list, rest, a, split, inside_left, S.Sweep.left(~F, ~field, a, b, split, rest, list, inside_right, marked)))))

def negation_decreases(~F: Kind(&2), ~field: K.Field<F>, ~first: F, ~second: F, +a: F, +b: F, +order: A.Algebra.le(~F, ~field, a, b)) ->
  A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a)):
  negation_sweep(~F, ~field, ~(first <> second <> Nil{}), first <> second <> Nil{}, a, b, order,
    S.Sweep.marked_members(~F, ~field, a, b, first <> second <> Nil{}, first <> second <> Nil{},
      S.Sweep.members_self(~F, ~field, first <> second <> Nil{})))
