import Base
import ../Field.bend as K
import ../FieldAlgebra.bend as A
import ../FieldOrder.bend as O
import ../Sweep.bend as S

def negation_decreases(~F: Kind(&2), ~field: K.Field<F>, ~first: F, ~second: F, +a: F, +b: F, +order: A.Algebra.le(~F, ~field, a, b)) ->
  A.Algebra.le(~F, ~field, A.Algebra.neg(~F, ~field, b), A.Algebra.neg(~F, ~field, a)):
  S.Sweep.monotone(~F, ~field, ~(first <> second <> Nil{}),
    ~S.Potential{x => A.Algebra.neg(~F, ~field, x), low => high => below => clean => O.FieldOrder.le_negate(~F, ~field, low, high, below)}, a, b, order)
