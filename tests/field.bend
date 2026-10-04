import Base
import ../Field.bend as K

def zero_add_le(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> K.Field.le(F, field)(K.Field.add(F, field)(K.Field.zero(F, field), a), a):
  K.Field.le_transitive(F, field)(
    K.Field.add(F, field)(K.Field.zero(F, field), a), K.Field.add(F, field)(a, K.Field.zero(F, field)), a,
    K.Field.add_commutative(F, field)(K.Field.zero(F, field), a),
    Pair.fst(K.Field.le(F, field)(K.Field.add(F, field)(a, K.Field.zero(F, field)), a), K.Field.le(F, field)(a, K.Field.add(F, field)(a, K.Field.zero(F, field))),
      K.Field.add_zero(F, field)(a)))
