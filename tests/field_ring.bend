import Base
import ../Field.bend as K
import ../FieldAlgebra.bend as A
import ../FieldRing.bend as R

def difference_of_squares(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) ->
  A.Algebra.Same(~F, ~field, A.Algebra.mul(~F, ~field, A.Algebra.add(~F, ~field, a, A.Algebra.neg(~F, ~field, b)), A.Algebra.add(~F, ~field, a, b)), A.Algebra.add(~F, ~field, A.Algebra.mul(~F, ~field, a, a), A.Algebra.neg(~F, ~field, A.Algebra.mul(~F, ~field, b, b)))):
  R.FieldRing.equal(~F, ~field, R.Value{a, R.Value{b, R.NoValues{}}},
    R.Multiply{R.Plus{R.Variable{0n}, R.Negate{R.Variable{1n}}}, R.Plus{R.Variable{0n}, R.Variable{1n}}},
    R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Negate{R.Multiply{R.Variable{1n}, R.Variable{1n}}}},
    {==})
