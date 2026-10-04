import Base
import ./Field.bend as K

def Algebra.zero(~F: Kind(&2), ~field: K.Field<F>) -> F:
  K.Field.zero(F, field)

def Algebra.one(~F: Kind(&2), ~field: K.Field<F>) -> F:
  K.Field.one(F, field)

def Algebra.half(~F: Kind(&2), ~field: K.Field<F>) -> F:
  K.Field.half(F, field)

def Algebra.add(~F: Kind(&2), ~field: K.Field<F>, a: F, b: F) -> F:
  K.Field.add(F, field)(a, b)

def Algebra.neg(~F: Kind(&2), ~field: K.Field<F>, a: F) -> F:
  K.Field.neg(F, field)(a)

def Algebra.mul(~F: Kind(&2), ~field: K.Field<F>, a: F, b: F) -> F:
  K.Field.mul(F, field)(a, b)

def Algebra.le(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> Kind(&2):
  K.Field.le(F, field)(a, b)

def Algebra.Same(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> Type:
  Algebra.le(~F, ~field, a, b) & Algebra.le(~F, ~field, b, a)

def Algebra.same_reflexive(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, a, a):
  (K.Field.le_reflexive(F, field)(a), K.Field.le_reflexive(F, field)(a))

def Algebra.same_symmetric(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, same: Algebra.Same(~F, ~field, a, b)) -> Algebra.Same(~F, ~field, b, a):
  (forward, backward) = same
  (backward, forward)

def Algebra.same_transitive(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, ab: Algebra.Same(~F, ~field, a, b), bc: Algebra.Same(~F, ~field, b, c)) -> Algebra.Same(~F, ~field, a, c):
  (ab_forward, ab_backward) = ab
  (bc_forward, bc_backward) = bc
  (K.Field.le_transitive(F, field)(a, b, c, ab_forward, bc_forward), K.Field.le_transitive(F, field)(c, b, a, bc_backward, ab_backward))

def Algebra.le_respects(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, +d: F, proof: Algebra.le(~F, ~field, a, b), ac: Algebra.Same(~F, ~field, a, c), bd: Algebra.Same(~F, ~field, b, d)) -> Algebra.le(~F, ~field, c, d):
  (ac_forward, ac_backward) = ac
  (bd_forward, bd_backward) = bd
  K.Field.le_transitive(F, field)(c, a, d, ac_backward, K.Field.le_transitive(F, field)(a, b, d, proof, bd_forward))

def Algebra.add_respects_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: Algebra.Same(~F, ~field, a, b)) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, a, c), Algebra.add(~F, ~field, b, c)):
  (forward, backward) = same
  (K.Field.le_add(F, field)(a, b, c, forward), K.Field.le_add(F, field)(b, a, c, backward))

def Algebra.add_commutes(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, a, b), Algebra.add(~F, ~field, b, a)):
  (K.Field.add_commutative(F, field)(a, b), K.Field.add_commutative(F, field)(b, a))

def Algebra.add_respects_right(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: Algebra.Same(~F, ~field, a, b)) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, c, a), Algebra.add(~F, ~field, c, b)):
  Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, c, a), Algebra.add(~F, ~field, a, c), Algebra.add(~F, ~field, c, b), Algebra.add_commutes(~F, ~field, c, a),
    Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, a, c), Algebra.add(~F, ~field, b, c), Algebra.add(~F, ~field, c, b), Algebra.add_respects_left(~F, ~field, a, b, c, same), Algebra.add_commutes(~F, ~field, b, c)))

def Algebra.add_respects(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, +d: F, ab: Algebra.Same(~F, ~field, a, b), cd: Algebra.Same(~F, ~field, c, d)) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, a, c), Algebra.add(~F, ~field, b, d)):
  Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, a, c), Algebra.add(~F, ~field, b, c), Algebra.add(~F, ~field, b, d), Algebra.add_respects_left(~F, ~field, a, b, c, ab), Algebra.add_respects_right(~F, ~field, c, d, b, cd))

def Algebra.add_associates(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, Algebra.add(~F, ~field, a, b), c), Algebra.add(~F, ~field, a, Algebra.add(~F, ~field, b, c))):
  K.Field.add_associative(F, field)(a, b, c)

def Algebra.add_zero(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, a, Algebra.zero(~F, ~field)), a):
  K.Field.add_zero(F, field)(a)

def Algebra.zero_add(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), a), a):
  Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), a), Algebra.add(~F, ~field, a, Algebra.zero(~F, ~field)), a, Algebra.add_commutes(~F, ~field, Algebra.zero(~F, ~field), a), Algebra.add_zero(~F, ~field, a))

def Algebra.add_neg(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, a, Algebra.neg(~F, ~field, a)), Algebra.zero(~F, ~field)):
  K.Field.add_neg(F, field)(a)

def Algebra.neg_add(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.add(~F, ~field, Algebra.neg(~F, ~field, a), a), Algebra.zero(~F, ~field)):
  Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, Algebra.neg(~F, ~field, a), a), Algebra.add(~F, ~field, a, Algebra.neg(~F, ~field, a)), Algebra.zero(~F, ~field), Algebra.add_commutes(~F, ~field, Algebra.neg(~F, ~field, a), a), Algebra.add_neg(~F, ~field, a))

def Algebra.add_cancel_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: Algebra.Same(~F, ~field, Algebra.add(~F, ~field, a, b), Algebra.add(~F, ~field, a, c))) -> Algebra.Same(~F, ~field, b, c):
  +inverse: F = Algebra.neg(~F, ~field, a)
  Algebra.same_transitive(~F, ~field, b, Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), b), c,
    Algebra.same_transitive(~F, ~field, b, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), b), Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), b),
      Algebra.same_symmetric(~F, ~field, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), b), b, Algebra.zero_add(~F, ~field, b)),
      Algebra.add_respects_left(~F, ~field, Algebra.zero(~F, ~field), Algebra.add(~F, ~field, inverse, a), b, Algebra.same_symmetric(~F, ~field, Algebra.add(~F, ~field, inverse, a), Algebra.zero(~F, ~field), Algebra.neg_add(~F, ~field, a)))),
    Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), b), Algebra.add(~F, ~field, inverse, Algebra.add(~F, ~field, a, c)), c,
      Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), b), Algebra.add(~F, ~field, inverse, Algebra.add(~F, ~field, a, b)), Algebra.add(~F, ~field, inverse, Algebra.add(~F, ~field, a, c)),
        Algebra.add_associates(~F, ~field, inverse, a, b),
        Algebra.add_respects_right(~F, ~field, Algebra.add(~F, ~field, a, b), Algebra.add(~F, ~field, a, c), inverse, same)),
      Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, inverse, Algebra.add(~F, ~field, a, c)), Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), c), c,
        Algebra.same_symmetric(~F, ~field, Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), c), Algebra.add(~F, ~field, inverse, Algebra.add(~F, ~field, a, c)), Algebra.add_associates(~F, ~field, inverse, a, c)),
        Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, Algebra.add(~F, ~field, inverse, a), c), Algebra.add(~F, ~field, Algebra.zero(~F, ~field), c), c,
          Algebra.add_respects_left(~F, ~field, Algebra.add(~F, ~field, inverse, a), Algebra.zero(~F, ~field), c, Algebra.neg_add(~F, ~field, a)),
          Algebra.zero_add(~F, ~field, c)))))

def Algebra.neg_respects(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, same: Algebra.Same(~F, ~field, a, b)) -> Algebra.Same(~F, ~field, Algebra.neg(~F, ~field, a), Algebra.neg(~F, ~field, b)):
  Algebra.add_cancel_left(~F, ~field, a, Algebra.neg(~F, ~field, a), Algebra.neg(~F, ~field, b),
    Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, a, Algebra.neg(~F, ~field, a)), Algebra.zero(~F, ~field), Algebra.add(~F, ~field, a, Algebra.neg(~F, ~field, b)), Algebra.add_neg(~F, ~field, a),
      Algebra.same_transitive(~F, ~field, Algebra.zero(~F, ~field), Algebra.add(~F, ~field, b, Algebra.neg(~F, ~field, b)), Algebra.add(~F, ~field, a, Algebra.neg(~F, ~field, b)),
        Algebra.same_symmetric(~F, ~field, Algebra.add(~F, ~field, b, Algebra.neg(~F, ~field, b)), Algebra.zero(~F, ~field), Algebra.add_neg(~F, ~field, b)),
        Algebra.add_respects_left(~F, ~field, b, a, Algebra.neg(~F, ~field, b), Algebra.same_symmetric(~F, ~field, a, b, same)))))

def Algebra.mul_respects_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: Algebra.Same(~F, ~field, a, b)) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, c)):
  K.Field.mul_respects(F, field)(a, b, c, same)

def Algebra.mul_commutes(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, a, b), Algebra.mul(~F, ~field, b, a)):
  (K.Field.mul_commutative(F, field)(a, b), K.Field.mul_commutative(F, field)(b, a))

def Algebra.mul_respects_right(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, same: Algebra.Same(~F, ~field, a, b)) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, c, a), Algebra.mul(~F, ~field, c, b)):
  Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, c, a), Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, c, b), Algebra.mul_commutes(~F, ~field, c, a),
    Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, c), Algebra.mul(~F, ~field, c, b), Algebra.mul_respects_left(~F, ~field, a, b, c, same), Algebra.mul_commutes(~F, ~field, b, c)))

def Algebra.mul_respects(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F, +d: F, ab: Algebra.Same(~F, ~field, a, b), cd: Algebra.Same(~F, ~field, c, d)) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, d)):
  Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, c), Algebra.mul(~F, ~field, b, d), Algebra.mul_respects_left(~F, ~field, a, b, c, ab), Algebra.mul_respects_right(~F, ~field, c, d, b, cd))

def Algebra.mul_associates(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, Algebra.mul(~F, ~field, a, b), c), Algebra.mul(~F, ~field, a, Algebra.mul(~F, ~field, b, c))):
  K.Field.mul_associative(F, field)(a, b, c)

def Algebra.mul_one(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, a, Algebra.one(~F, ~field)), a):
  K.Field.mul_one(F, field)(a)

def Algebra.one_mul(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, Algebra.one(~F, ~field), a), a):
  Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, Algebra.one(~F, ~field), a), Algebra.mul(~F, ~field, a, Algebra.one(~F, ~field)), a, Algebra.mul_commutes(~F, ~field, Algebra.one(~F, ~field), a), Algebra.mul_one(~F, ~field, a))

def Algebra.distributes_left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, a, Algebra.add(~F, ~field, b, c)), Algebra.add(~F, ~field, Algebra.mul(~F, ~field, a, b), Algebra.mul(~F, ~field, a, c))):
  K.Field.distributive(F, field)(a, b, c)

def Algebra.distributes_right(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +c: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, Algebra.add(~F, ~field, a, b), c), Algebra.add(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, c))):
  Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, Algebra.add(~F, ~field, a, b), c), Algebra.mul(~F, ~field, c, Algebra.add(~F, ~field, a, b)), Algebra.add(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, c)),
    Algebra.mul_commutes(~F, ~field, Algebra.add(~F, ~field, a, b), c),
    Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, c, Algebra.add(~F, ~field, a, b)), Algebra.add(~F, ~field, Algebra.mul(~F, ~field, c, a), Algebra.mul(~F, ~field, c, b)), Algebra.add(~F, ~field, Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, b, c)),
      Algebra.distributes_left(~F, ~field, c, a, b),
      Algebra.add_respects(~F, ~field, Algebra.mul(~F, ~field, c, a), Algebra.mul(~F, ~field, a, c), Algebra.mul(~F, ~field, c, b), Algebra.mul(~F, ~field, b, c), Algebra.mul_commutes(~F, ~field, c, a), Algebra.mul_commutes(~F, ~field, c, b))))

def Algebra.mul_zero(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, a, Algebra.zero(~F, ~field)), Algebra.zero(~F, ~field)):
  +product: F = Algebra.mul(~F, ~field, a, Algebra.zero(~F, ~field))
  Algebra.add_cancel_left(~F, ~field, product, product, Algebra.zero(~F, ~field),
    Algebra.same_transitive(~F, ~field, Algebra.add(~F, ~field, product, product), Algebra.mul(~F, ~field, a, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), Algebra.zero(~F, ~field))), Algebra.add(~F, ~field, product, Algebra.zero(~F, ~field)),
      Algebra.same_symmetric(~F, ~field, Algebra.mul(~F, ~field, a, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), Algebra.zero(~F, ~field))), Algebra.add(~F, ~field, product, product), Algebra.distributes_left(~F, ~field, a, Algebra.zero(~F, ~field), Algebra.zero(~F, ~field))),
      Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, a, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), Algebra.zero(~F, ~field))), product, Algebra.add(~F, ~field, product, Algebra.zero(~F, ~field)),
        Algebra.mul_respects_right(~F, ~field, Algebra.add(~F, ~field, Algebra.zero(~F, ~field), Algebra.zero(~F, ~field)), Algebra.zero(~F, ~field), a, Algebra.add_zero(~F, ~field, Algebra.zero(~F, ~field))),
        Algebra.same_symmetric(~F, ~field, Algebra.add(~F, ~field, product, Algebra.zero(~F, ~field)), product, Algebra.add_zero(~F, ~field, product)))))

def Algebra.zero_mul(~F: Kind(&2), ~field: K.Field<F>, +a: F) -> Algebra.Same(~F, ~field, Algebra.mul(~F, ~field, Algebra.zero(~F, ~field), a), Algebra.zero(~F, ~field)):
  Algebra.same_transitive(~F, ~field, Algebra.mul(~F, ~field, Algebra.zero(~F, ~field), a), Algebra.mul(~F, ~field, a, Algebra.zero(~F, ~field)), Algebra.zero(~F, ~field), Algebra.mul_commutes(~F, ~field, Algebra.zero(~F, ~field), a), Algebra.mul_zero(~F, ~field, a))
