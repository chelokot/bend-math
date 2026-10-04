import Base
import ../Field.bend as K
import ../FieldAlgebra.bend as A
import ../FieldOrder.bend as O

def strict_pair(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +strict: O.FieldOrder.Strict(~F, ~field, a, b)) -> O.FieldOrder.Lt(~F, ~field, a, b) & O.FieldOrder.Lt(~F, ~field, a, b):
  (O.FieldOrder.lt_of(~F, ~field, a, b, strict), O.FieldOrder.lt_of(~F, ~field, a, b, strict))

def strict_twice(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, less: O.FieldOrder.Lt(~F, ~field, a, b)) -> O.FieldOrder.Lt(~F, ~field, a, b) & O.FieldOrder.Lt(~F, ~field, a, b):
  strict_pair(~F, ~field, a, b, O.FieldOrder.strict_of(~F, ~field, a, b, less))
