import Base
import ../Field.bend as K
import ../FieldAlgebra.bend as A
import ../FieldRing.bend as R
import ../Certificate.bend as C

def unit_circle() -> R.FieldRing.Expr:
  R.Plus{R.Plus{R.Multiply{R.Variable{0n}, R.Variable{0n}}, R.Multiply{R.Variable{1n}, R.Variable{1n}}}, R.Negate{R.Number{1n}}}

def cosine_at_most_one(~F: Kind(&2), ~field: K.Field<F>, +cosine: F, +sine: F,
  below: A.Algebra.le(~F, ~field, R.FieldRing.value(~F, ~field, R.Value{cosine, R.Value{sine, R.NoValues{}}}, unit_circle()), A.Algebra.zero(~F, ~field)),
  above: A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), R.FieldRing.value(~F, ~field, R.Value{cosine, R.Value{sine, R.NoValues{}}}, unit_circle()))) ->
  A.Algebra.le(~F, ~field, A.Algebra.zero(~F, ~field), R.FieldRing.value(~F, ~field, R.Value{cosine, R.Value{sine, R.NoValues{}}}, R.Plus{R.Number{1n}, R.Negate{R.Variable{0n}}})):
  C.Certificate.nonnegative(~F, ~field, R.Value{cosine, R.Value{sine, R.NoValues{}}},
    C.NoExprs{}, Unit{},
    C.MoreExprs{unit_circle(), C.NoExprs{}}, C.Both{C.Both{below, above}, Unit{}},
    1n, R.Plus{R.Number{1n}, R.Negate{R.Variable{0n}}},
    C.MoreTerms{C.Product{1n, C.NoIndices{}, R.Plus{R.Number{1n}, R.Negate{R.Variable{0n}}}},
      C.MoreTerms{C.Product{1n, C.NoIndices{}, R.Variable{1n}},
        C.MoreTerms{C.Multiple{0n, R.Negate{R.Number{1n}}}, C.NoTerms{}}}},
    {==})
