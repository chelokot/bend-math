import Base
import ./Natural.bend as N
import ./Integer.bend as Z

type Rational is Data:
  Fraction{positive: Nat, negative: Nat, denominator_predecessor: Nat}

def Rational.zero() -> Rational:
  Fraction{0n, 0n, 0n}

def Rational.one() -> Rational:
  Fraction{1n, 0n, 0n}

def Rational.of_integer(x: Z.Integer) -> Rational:
  match x:
    case Z.ZPos{magnitude}:
      Fraction{magnitude, 0n, 0n}
    case Z.ZNeg{predecessor}:
      Fraction{0n, 1n+predecessor, 0n}

def Rational.of_nat(n: Nat) -> Rational:
  Fraction{n, 0n, 0n}

def Rational.positive(x: Rational) -> Nat:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      positive

def Rational.negative(x: Rational) -> Nat:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      negative

def Rational.denominator(x: Rational) -> Nat:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      1n+denominator_predecessor

def Rational.denominator_product(a: Nat, +b: Nat) -> Nat:
  Nat.add(b, Nat.mul(a, 1n+b))

def Rational.denominator_product_spec(a: Nat, +b: Nat) -> {1n+Rational.denominator_product(a, b) == Nat.mul(1n+a, 1n+b) : Nat}:
  {==}

def Rational.denominator_product_commutative(+a: Nat, +b: Nat) -> {Rational.denominator_product(a, b) == Rational.denominator_product(b, a) : Nat}:
  N.Natural.successor_injective(Rational.denominator_product(a, b), Rational.denominator_product(b, a),
    Equal.trans(Nat,
      1n+Rational.denominator_product(a, b),
      Nat.mul(1n+a, 1n+b),
      1n+Rational.denominator_product(b, a),
      Rational.denominator_product_spec(a, b),
      Equal.trans(Nat,
        Nat.mul(1n+a, 1n+b),
        Nat.mul(1n+b, 1n+a),
        1n+Rational.denominator_product(b, a),
        N.Natural.mul_commutative(1n+a, 1n+b),
        Equal.sym(Nat,
          1n+Rational.denominator_product(b, a),
          Nat.mul(1n+b, 1n+a),
          Rational.denominator_product_spec(b, a)))))

def Rational.denominator_product_associative(+a: Nat, +b: Nat, +c: Nat) ->
  {Rational.denominator_product(Rational.denominator_product(a, b), c) ==
   Rational.denominator_product(a, Rational.denominator_product(b, c)) : Nat}:
  +ab: Nat = Rational.denominator_product(a, b)
  +bc: Nat = Rational.denominator_product(b, c)
  N.Natural.successor_injective(Rational.denominator_product(ab, c), Rational.denominator_product(a, bc),
    Equal.trans(Nat,
      1n+Rational.denominator_product(ab, c),
      Nat.mul(1n+ab, 1n+c),
      1n+Rational.denominator_product(a, bc),
      Rational.denominator_product_spec(ab, c),
      Equal.trans(Nat,
        Nat.mul(1n+ab, 1n+c),
        Nat.mul(Nat.mul(1n+a, 1n+b), 1n+c),
        1n+Rational.denominator_product(a, bc),
        Equal.cong(Nat, Nat, z => Nat.mul(z, 1n+c), 1n+ab, Nat.mul(1n+a, 1n+b), Rational.denominator_product_spec(a, b)),
        Equal.trans(Nat,
          Nat.mul(Nat.mul(1n+a, 1n+b), 1n+c),
          Nat.mul(1n+a, Nat.mul(1n+b, 1n+c)),
          1n+Rational.denominator_product(a, bc),
          N.Natural.mul_associative(1n+a, 1n+b, 1n+c),
          Equal.trans(Nat,
            Nat.mul(1n+a, Nat.mul(1n+b, 1n+c)),
            Nat.mul(1n+a, 1n+bc),
            1n+Rational.denominator_product(a, bc),
            Equal.cong(Nat, Nat, z => Nat.mul(1n+a, z), Nat.mul(1n+b, 1n+c), 1n+bc,
              Equal.sym(Nat, 1n+bc, Nat.mul(1n+b, 1n+c), Rational.denominator_product_spec(b, c))),
            Equal.sym(Nat,
              1n+Rational.denominator_product(a, bc),
              Nat.mul(1n+a, 1n+bc),
              Rational.denominator_product_spec(a, bc)))))))

def Rational.fraction_congruent(+ap: Nat, +an: Nat, +ad: Nat, +bp: Nat, +bn: Nat, +bd: Nat,
  ep: {ap == bp : Nat}, en: {an == bn : Nat}, ed: {ad == bd : Nat}) ->
  {Fraction{ap, an, ad} == Fraction{bp, bn, bd} : Rational}:
  Equal.trans(Rational,
    Fraction{ap, an, ad}, Fraction{bp, an, ad}, Fraction{bp, bn, bd},
    Equal.cong(Nat, Rational, z => Fraction{z, an, ad}, ap, bp, ep),
    Equal.trans(Rational,
      Fraction{bp, an, ad}, Fraction{bp, bn, ad}, Fraction{bp, bn, bd},
      Equal.cong(Nat, Rational, z => Fraction{bp, z, ad}, an, bn, en),
      Equal.cong(Nat, Rational, z => Fraction{bp, bn, z}, ad, bd, ed)))

def Rational.add(a: Rational, b: Rational) -> Rational:
  match a b:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd}:
      Fraction{
        Nat.add(Nat.mul(ap, 1n+bd), Nat.mul(bp, 1n+ad)),
        Nat.add(Nat.mul(an, 1n+bd), Nat.mul(bn, 1n+ad)),
        Rational.denominator_product(ad, bd)
      }

def Rational.add_commutative(a: Rational, b: Rational) -> {Rational.add(a, b) == Rational.add(b, a) : Rational}:
  match a b:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd}:
      Rational.fraction_congruent(
        Nat.add(Nat.mul(ap, 1n+bd), Nat.mul(bp, 1n+ad)),
        Nat.add(Nat.mul(an, 1n+bd), Nat.mul(bn, 1n+ad)),
        Rational.denominator_product(ad, bd),
        Nat.add(Nat.mul(bp, 1n+ad), Nat.mul(ap, 1n+bd)),
        Nat.add(Nat.mul(bn, 1n+ad), Nat.mul(an, 1n+bd)),
        Rational.denominator_product(bd, ad),
        N.Natural.add_commutative(Nat.mul(ap, 1n+bd), Nat.mul(bp, 1n+ad)),
        N.Natural.add_commutative(Nat.mul(an, 1n+bd), Nat.mul(bn, 1n+ad)),
        Rational.denominator_product_commutative(ad, bd))

def Rational.add_associative_numerator(+a: Nat, +b: Nat, +c: Nat, +ad: Nat, +bd: Nat, +cd: Nat) ->
  {Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, 1n+bd), Nat.mul(b, 1n+ad)), 1n+cd),
     Nat.mul(c, 1n+Rational.denominator_product(ad, bd))) ==
   Nat.add(
     Nat.mul(a, 1n+Rational.denominator_product(bd, cd)),
     Nat.mul(Nat.add(Nat.mul(b, 1n+cd), Nat.mul(c, 1n+bd)), 1n+ad)) : Nat}:
  +da: Nat = 1n+ad
  +db: Nat = 1n+bd
  +dc: Nat = 1n+cd
  +ab: Nat = Nat.add(Nat.mul(a, db), Nat.mul(b, da))
  +bc: Nat = Nat.add(Nat.mul(b, dc), Nat.mul(c, db))
  Equal.trans(Nat,
    Nat.add(Nat.mul(ab, dc), Nat.mul(c, 1n+Rational.denominator_product(ad, bd))),
    Nat.add(Nat.mul(ab, dc), Nat.mul(c, Nat.mul(da, db))),
    Nat.add(Nat.mul(a, 1n+Rational.denominator_product(bd, cd)), Nat.mul(bc, da)),
    Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(ab, dc), Nat.mul(c, z)),
      1n+Rational.denominator_product(ad, bd), Nat.mul(da, db),
      Rational.denominator_product_spec(ad, bd)),
    Equal.trans(Nat,
      Nat.add(Nat.mul(ab, dc), Nat.mul(c, Nat.mul(da, db))),
      Nat.add(Nat.mul(a, Nat.mul(db, dc)), Nat.mul(bc, da)),
      Nat.add(Nat.mul(a, 1n+Rational.denominator_product(bd, cd)), Nat.mul(bc, da)),
      N.Natural.fraction_sum_associative(a, b, c, da, db, dc),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(a, z), Nat.mul(bc, da)),
        Nat.mul(db, dc), 1n+Rational.denominator_product(bd, cd),
        Equal.sym(Nat,
          1n+Rational.denominator_product(bd, cd), Nat.mul(db, dc),
          Rational.denominator_product_spec(bd, cd)))))

def Rational.add_associative(a: Rational, b: Rational, c: Rational) -> {Rational.add(Rational.add(a, b), c) == Rational.add(a, Rational.add(b, c)) : Rational}:
  match a b c:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd} Fraction{+cp, +cn, +cd}:
      Rational.fraction_congruent(
        Nat.add(Nat.mul(Nat.add(Nat.mul(ap, 1n+bd), Nat.mul(bp, 1n+ad)), 1n+cd), Nat.mul(cp, 1n+Rational.denominator_product(ad, bd))),
        Nat.add(Nat.mul(Nat.add(Nat.mul(an, 1n+bd), Nat.mul(bn, 1n+ad)), 1n+cd), Nat.mul(cn, 1n+Rational.denominator_product(ad, bd))),
        Rational.denominator_product(Rational.denominator_product(ad, bd), cd),
        Nat.add(Nat.mul(ap, 1n+Rational.denominator_product(bd, cd)), Nat.mul(Nat.add(Nat.mul(bp, 1n+cd), Nat.mul(cp, 1n+bd)), 1n+ad)),
        Nat.add(Nat.mul(an, 1n+Rational.denominator_product(bd, cd)), Nat.mul(Nat.add(Nat.mul(bn, 1n+cd), Nat.mul(cn, 1n+bd)), 1n+ad)),
        Rational.denominator_product(ad, Rational.denominator_product(bd, cd)),
        Rational.add_associative_numerator(ap, bp, cp, ad, bd, cd),
        Rational.add_associative_numerator(an, bn, cn, ad, bd, cd),
        Rational.denominator_product_associative(ad, bd, cd))

def Rational.add_zero(x: Rational) -> {Rational.add(x, Rational.zero()) == x : Rational}:
  match x:
    case Fraction{+xp, +xn, +xd}:
      Rational.fraction_congruent(
        Nat.add(Nat.mul(xp, 1n), 0n),
        Nat.add(Nat.mul(xn, 1n), 0n),
        Rational.denominator_product(xd, 0n),
        xp, xn, xd,
        Equal.trans(Nat,
          Nat.add(Nat.mul(xp, 1n), 0n), Nat.mul(xp, 1n), xp,
          N.Natural.add_zero(Nat.mul(xp, 1n)), N.Natural.mul_one(xp)),
        Equal.trans(Nat,
          Nat.add(Nat.mul(xn, 1n), 0n), Nat.mul(xn, 1n), xn,
          N.Natural.add_zero(Nat.mul(xn, 1n)), N.Natural.mul_one(xn)),
        N.Natural.mul_one(xd))

def Rational.zero_add(+x: Rational) -> {Rational.add(Rational.zero(), x) == x : Rational}:
  Equal.trans(Rational,
    Rational.add(Rational.zero(), x), Rational.add(x, Rational.zero()), x,
    Rational.add_commutative(Rational.zero(), x),
    Rational.add_zero(x))

def Rational.neg(x: Rational) -> Rational:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      Fraction{negative, positive, denominator_predecessor}

def Rational.neg_involutive(x: Rational) -> {Rational.neg(Rational.neg(x)) == x : Rational}:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      {==}

def Rational.sub(a: Rational, b: Rational) -> Rational:
  Rational.add(a, Rational.neg(b))

def Rational.mul(a: Rational, b: Rational) -> Rational:
  match a b:
    case Fraction{+ap, +an, ad} Fraction{+bp, +bn, bd}:
      Fraction{
        Nat.add(Nat.mul(ap, bp), Nat.mul(an, bn)),
        Nat.add(Nat.mul(ap, bn), Nat.mul(an, bp)),
        Rational.denominator_product(ad, bd)
      }

def Rational.mul_commutative(a: Rational, b: Rational) -> {Rational.mul(a, b) == Rational.mul(b, a) : Rational}:
  match a b:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd}:
      Rational.fraction_congruent(
        Nat.add(Nat.mul(ap, bp), Nat.mul(an, bn)),
        Nat.add(Nat.mul(ap, bn), Nat.mul(an, bp)),
        Rational.denominator_product(ad, bd),
        Nat.add(Nat.mul(bp, ap), Nat.mul(bn, an)),
        Nat.add(Nat.mul(bp, an), Nat.mul(bn, ap)),
        Rational.denominator_product(bd, ad),
        N.Natural.eq_add_congruent(
          Nat.mul(ap, bp), Nat.mul(an, bn), Nat.mul(bp, ap), Nat.mul(bn, an),
          N.Natural.mul_commutative(ap, bp), N.Natural.mul_commutative(an, bn)),
        Equal.trans(Nat,
          Nat.add(Nat.mul(ap, bn), Nat.mul(an, bp)),
          Nat.add(Nat.mul(bn, ap), Nat.mul(bp, an)),
          Nat.add(Nat.mul(bp, an), Nat.mul(bn, ap)),
          N.Natural.eq_add_congruent(
            Nat.mul(ap, bn), Nat.mul(an, bp), Nat.mul(bn, ap), Nat.mul(bp, an),
            N.Natural.mul_commutative(ap, bn), N.Natural.mul_commutative(an, bp)),
          N.Natural.add_commutative(Nat.mul(bn, ap), Nat.mul(bp, an))),
        Rational.denominator_product_commutative(ad, bd))

def Rational.mul_associative(a: Rational, b: Rational, c: Rational) -> {Rational.mul(Rational.mul(a, b), c) == Rational.mul(a, Rational.mul(b, c)) : Rational}:
  match a b c:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd} Fraction{+cp, +cn, +cd}:
      Rational.fraction_congruent(
        Nat.add(
          Nat.mul(Nat.add(Nat.mul(ap, bp), Nat.mul(an, bn)), cp),
          Nat.mul(Nat.add(Nat.mul(ap, bn), Nat.mul(an, bp)), cn)),
        Nat.add(
          Nat.mul(Nat.add(Nat.mul(ap, bp), Nat.mul(an, bn)), cn),
          Nat.mul(Nat.add(Nat.mul(ap, bn), Nat.mul(an, bp)), cp)),
        Rational.denominator_product(Rational.denominator_product(ad, bd), cd),
        Nat.add(
          Nat.mul(ap, Nat.add(Nat.mul(bp, cp), Nat.mul(bn, cn))),
          Nat.mul(an, Nat.add(Nat.mul(bp, cn), Nat.mul(bn, cp)))),
        Nat.add(
          Nat.mul(ap, Nat.add(Nat.mul(bp, cn), Nat.mul(bn, cp))),
          Nat.mul(an, Nat.add(Nat.mul(bp, cp), Nat.mul(bn, cn)))),
        Rational.denominator_product(ad, Rational.denominator_product(bd, cd)),
        N.Natural.signed_product_associative(ap, an, bp, bn, cp, cn),
        N.Natural.signed_product_associative(ap, an, bp, bn, cn, cp),
        Rational.denominator_product_associative(ad, bd, cd))

def Rational.mul_one(x: Rational) -> {Rational.mul(x, Rational.one()) == x : Rational}:
  match x:
    case Fraction{+xp, +xn, +xd}:
      Rational.fraction_congruent(
        Nat.add(Nat.mul(xp, 1n), Nat.mul(xn, 0n)),
        Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n)),
        Rational.denominator_product(xd, 0n),
        xp, xn, xd,
        Equal.trans(Nat,
          Nat.add(Nat.mul(xp, 1n), Nat.mul(xn, 0n)),
          Nat.add(xp, 0n), xp,
          N.Natural.eq_add_congruent(Nat.mul(xp, 1n), Nat.mul(xn, 0n), xp, 0n,
            N.Natural.mul_one(xp), N.Natural.mul_zero(xn)),
          N.Natural.add_zero(xp)),
        Equal.trans(Nat,
          Nat.add(Nat.mul(xp, 0n), Nat.mul(xn, 1n)),
          Nat.add(0n, xn), xn,
          N.Natural.eq_add_congruent(Nat.mul(xp, 0n), Nat.mul(xn, 1n), 0n, xn,
            N.Natural.mul_zero(xp), N.Natural.mul_one(xn)),
          {==}),
        N.Natural.mul_one(xd))

def Rational.one_mul(+x: Rational) -> {Rational.mul(Rational.one(), x) == x : Rational}:
  Equal.trans(Rational,
    Rational.mul(Rational.one(), x), Rational.mul(x, Rational.one()), x,
    Rational.mul_commutative(Rational.one(), x),
    Rational.mul_one(x))

def Rational.left_cross(+x: Rational, +y: Rational) -> Nat:
  Nat.add(Nat.mul(Rational.positive(x), Rational.denominator(y)), Nat.mul(Rational.negative(y), Rational.denominator(x)))

def Rational.right_cross(+x: Rational, +y: Rational) -> Nat:
  Nat.add(Nat.mul(Rational.positive(y), Rational.denominator(x)), Nat.mul(Rational.negative(x), Rational.denominator(y)))

def Rational.Eq(+x: Rational, +y: Rational) -> Type:
  {Rational.left_cross(x, y) == Rational.right_cross(x, y) : Nat}

def Rational.eq_zero_if_balanced(+positive: Nat, +negative: Nat, +denominator_predecessor: Nat, proof: {positive == negative : Nat}) -> Rational.Eq(Fraction{positive, negative, denominator_predecessor}, Rational.zero()):
  Equal.trans(Nat,
    Nat.add(Nat.mul(positive, 1n), 0n),
    Nat.add(0n, Nat.mul(positive, 1n)),
    Nat.add(0n, Nat.mul(negative, 1n)),
    N.Natural.add_commutative(Nat.mul(positive, 1n), 0n),
    Equal.cong(Nat, Nat, z => Nat.add(0n, Nat.mul(z, 1n)), positive, negative, proof))

def Rational.add_neg_self(x: Rational) -> Rational.Eq(Rational.add(x, Rational.neg(x)), Rational.zero()):
  match x:
    case Fraction{+positive, +negative, +denominator_predecessor}:
      Rational.eq_zero_if_balanced(
        Nat.add(Nat.mul(positive, 1n+denominator_predecessor), Nat.mul(negative, 1n+denominator_predecessor)),
        Nat.add(Nat.mul(negative, 1n+denominator_predecessor), Nat.mul(positive, 1n+denominator_predecessor)),
        Rational.denominator_product(denominator_predecessor, denominator_predecessor),
        N.Natural.add_commutative(
          Nat.mul(positive, 1n+denominator_predecessor),
          Nat.mul(negative, 1n+denominator_predecessor)))

def Rational.mul_zero(x: Rational) -> Rational.Eq(Rational.mul(x, Rational.zero()), Rational.zero()):
  match x:
    case Fraction{+positive, +negative, +denominator_predecessor}:
      Rational.eq_zero_if_balanced(
        Nat.add(Nat.mul(positive, 0n), Nat.mul(negative, 0n)),
        Nat.add(Nat.mul(positive, 0n), Nat.mul(negative, 0n)),
        Rational.denominator_product(denominator_predecessor, 0n), {==})

def Rational.Le(+x: Rational, +y: Rational) -> Type:
  N.Natural.Le(Rational.left_cross(x, y), Rational.right_cross(x, y))

def Rational.le_total(+x: Rational, +y: Rational) -> Or(Rational.Le(x, y), Rational.Le(y, x)):
  N.Natural.le_total(Rational.left_cross(x, y), Rational.right_cross(x, y))

def Rational.zero_ne_one(proof: Rational.Eq(Rational.zero(), Rational.one())) -> Empty:
  N.Natural.zero_not_successor(0n, proof)

def Rational.Close(+x: Rational, +y: Rational, +left_error: Rational, +right_error: Rational) -> Type:
  Rational.Le(x, Rational.add(y, Rational.add(left_error, right_error))) & Rational.Le(y, Rational.add(x, Rational.add(right_error, left_error)))

def Rational.close_symmetric(+x: Rational, +y: Rational, +left_error: Rational, +right_error: Rational, proof: Rational.Close(x, y, left_error, right_error)) -> Rational.Close(y, x, right_error, left_error):
  (forward, backward) = proof
  (backward, forward)

def Rational.eq_reflexive(x: Rational) -> Rational.Eq(x, x):
  {==}

def Rational.eq_symmetric(+x: Rational, +y: Rational, proof: Rational.Eq(x, y)) -> Rational.Eq(y, x):
  Equal.sym(Nat, Rational.left_cross(x, y), Rational.right_cross(x, y), proof)

def Rational.eq_negated(+x: Rational, +y: Rational, proof: Rational.Eq(x, y)) -> Rational.Eq(Rational.neg(x), Rational.neg(y)):
  match x y:
    case Fraction{+xp, +xn, +xd} Fraction{+yp, +yn, +yd}:
      N.Natural.eq_add_swap(
        Nat.mul(xn, 1n+yd), Nat.mul(yp, 1n+xd),
        Nat.mul(yn, 1n+xd), Nat.mul(xp, 1n+yd),
        Rational.eq_symmetric(Fraction{xp, xn, xd}, Fraction{yp, yn, yd}, proof))

def Rational.le_reflexive(+x: Rational) -> Rational.Le(x, x):
  N.Natural.le_reflexive(Rational.left_cross(x, x))

def Rational.le_antisymmetric(+x: Rational, +y: Rational, xy: Rational.Le(x, y), yx: Rational.Le(y, x)) -> Rational.Eq(x, y):
  N.Natural.le_antisymmetric(Rational.left_cross(x, y), Rational.right_cross(x, y), xy, yx)

def Rational.eq_implies_le(+x: Rational, +y: Rational, proof: Rational.Eq(x, y)) -> Rational.Le(x, y):
  %proof : N.Natural.Le(Rational.left_cross(x, y), _)
  N.Natural.le_reflexive(Rational.left_cross(x, y))

def Rational.le_negated(+x: Rational, +y: Rational, proof: Rational.Le(x, y)) -> Rational.Le(Rational.neg(y), Rational.neg(x)):
  match x y:
    case Fraction{+xp, +xn, +xd} Fraction{+yp, +yn, +yd}:
      N.Natural.le_congruent(
        Nat.add(Nat.mul(xp, 1n+yd), Nat.mul(yn, 1n+xd)),
        Nat.add(Nat.mul(yp, 1n+xd), Nat.mul(xn, 1n+yd)),
        Nat.add(Nat.mul(yn, 1n+xd), Nat.mul(xp, 1n+yd)),
        Nat.add(Nat.mul(xn, 1n+yd), Nat.mul(yp, 1n+xd)),
        proof,
        N.Natural.add_commutative(Nat.mul(xp, 1n+yd), Nat.mul(yn, 1n+xd)),
        N.Natural.add_commutative(Nat.mul(yp, 1n+xd), Nat.mul(xn, 1n+yd)))

def Rational.le_transitive_core(
  +xp: Nat, +xn: Nat, +xd: Nat,
  +yp: Nat, +yn: Nat, +yd: Nat,
  +zp: Nat, +zn: Nat, +zd: Nat,
  xy: N.Natural.Le(
    Nat.add(Nat.mul(xp, 1n+yd), Nat.mul(yn, 1n+xd)),
    Nat.add(Nat.mul(yp, 1n+xd), Nat.mul(xn, 1n+yd))),
  yz: N.Natural.Le(
    Nat.add(Nat.mul(yp, 1n+zd), Nat.mul(zn, 1n+yd)),
    Nat.add(Nat.mul(zp, 1n+yd), Nat.mul(yn, 1n+zd)))) ->
  N.Natural.Le(
    Nat.add(Nat.mul(xp, 1n+zd), Nat.mul(zn, 1n+xd)),
    Nat.add(Nat.mul(zp, 1n+xd), Nat.mul(xn, 1n+zd))):
  +dx: Nat = 1n+xd
  +dy: Nat = 1n+yd
  +dz: Nat = 1n+zd
  +a = Nat.mul(Nat.mul(xp, dy), dz)
  +b = Nat.mul(Nat.mul(yp, dx), dz)
  +c = Nat.mul(Nat.mul(yn, dx), dz)
  +d = Nat.mul(Nat.mul(xn, dy), dz)
  +e = Nat.mul(Nat.mul(zn, dy), dx)
  +f = Nat.mul(Nat.mul(zp, dy), dx)
  first = N.Natural.le_cross_scaled(Nat.mul(xp, dy), Nat.mul(yp, dx), Nat.mul(yn, dx), Nat.mul(xn, dy), dz, xy)
  second_scaled = N.Natural.le_cross_scaled(Nat.mul(yp, dz), Nat.mul(zp, dy), Nat.mul(zn, dy), Nat.mul(yn, dz), dx, yz)
  second = N.Natural.le_congruent(
    Nat.add(Nat.mul(Nat.mul(yp, dz), dx), e),
    Nat.add(f, Nat.mul(Nat.mul(yn, dz), dx)),
    Nat.add(b, e), Nat.add(c, f), second_scaled,
    N.Natural.eq_add_congruent(
      Nat.mul(Nat.mul(yp, dz), dx), e, b, e,
      N.Natural.mul_last_swap(yp, dz, dx), {==}),
    Equal.trans(Nat,
      Nat.add(f, Nat.mul(Nat.mul(yn, dz), dx)),
      Nat.add(f, c), Nat.add(c, f),
      N.Natural.eq_add_congruent(f, Nat.mul(Nat.mul(yn, dz), dx), f, c,
        {==}, N.Natural.mul_last_swap(yn, dz, dx)),
      N.Natural.add_commutative(f, c)))
  balanced = N.Natural.le_balance(a, b, c, d, e, f, first, second)
  +left = Nat.add(Nat.mul(xp, dz), Nat.mul(zn, dx))
  +right = Nat.add(Nat.mul(zp, dx), Nat.mul(xn, dz))
  left_scaled = Equal.trans(Nat,
    Nat.add(a, e),
    Nat.add(Nat.mul(Nat.mul(xp, dz), dy), Nat.mul(Nat.mul(zn, dx), dy)),
    Nat.mul(left, dy),
    N.Natural.eq_add_congruent(a, e,
      Nat.mul(Nat.mul(xp, dz), dy), Nat.mul(Nat.mul(zn, dx), dy),
      N.Natural.mul_last_swap(xp, dy, dz),
      N.Natural.mul_last_swap(zn, dy, dx)),
    Equal.sym(Nat,
      Nat.mul(left, dy),
      Nat.add(Nat.mul(Nat.mul(xp, dz), dy), Nat.mul(Nat.mul(zn, dx), dy)),
      N.Natural.mul_add_left(Nat.mul(xp, dz), Nat.mul(zn, dx), dy)))
  right_scaled = Equal.trans(Nat,
    Nat.add(d, f),
    Nat.add(Nat.mul(Nat.mul(xn, dz), dy), Nat.mul(Nat.mul(zp, dx), dy)),
    Nat.mul(right, dy),
    N.Natural.eq_add_congruent(d, f,
      Nat.mul(Nat.mul(xn, dz), dy), Nat.mul(Nat.mul(zp, dx), dy),
      N.Natural.mul_last_swap(xn, dy, dz),
      N.Natural.mul_last_swap(zp, dy, dx)),
    Equal.trans(Nat,
      Nat.add(Nat.mul(Nat.mul(xn, dz), dy), Nat.mul(Nat.mul(zp, dx), dy)),
      Nat.add(Nat.mul(Nat.mul(zp, dx), dy), Nat.mul(Nat.mul(xn, dz), dy)),
      Nat.mul(right, dy),
      N.Natural.add_commutative(Nat.mul(Nat.mul(xn, dz), dy), Nat.mul(Nat.mul(zp, dx), dy)),
      Equal.sym(Nat,
        Nat.mul(right, dy),
        Nat.add(Nat.mul(Nat.mul(zp, dx), dy), Nat.mul(Nat.mul(xn, dz), dy)),
        N.Natural.mul_add_left(Nat.mul(zp, dx), Nat.mul(xn, dz), dy))))
  N.Natural.le_mul_right_cancel_positive(yd, left, right,
    N.Natural.le_congruent(Nat.add(a, e), Nat.add(d, f), Nat.mul(left, dy), Nat.mul(right, dy), balanced, left_scaled, right_scaled))

def Rational.le_transitive(+x: Rational, +y: Rational, +z: Rational, xy: Rational.Le(x, y), yz: Rational.Le(y, z)) -> Rational.Le(x, z):
  match x y z:
    case Fraction{xp, xn, xd} Fraction{yp, yn, yd} Fraction{zp, zn, zd}:
      Rational.le_transitive_core(xp, xn, xd, yp, yn, yd, zp, zn, zd, xy, yz)

def Rational.eq_both_le(+x: Rational, +y: Rational, equality: Rational.Eq(x, y)) -> Rational.Le(x, y) & Rational.Le(y, x):
  N.Natural.le_both_from_eq(Rational.left_cross(x, y), Rational.right_cross(x, y), equality)

def Rational.eq_transitive_bounds(+x: Rational, +y: Rational, +z: Rational,
  xy_bounds: Rational.Le(x, y) & Rational.Le(y, x),
  yz_bounds: Rational.Le(y, z) & Rational.Le(z, y)) -> Rational.Eq(x, z):
  (xy_forward, xy_backward) = xy_bounds
  (yz_forward, yz_backward) = yz_bounds
  Rational.le_antisymmetric(x, z,
    Rational.le_transitive(x, y, z, xy_forward, yz_forward),
    Rational.le_transitive(z, y, x, yz_backward, xy_backward))

def Rational.eq_transitive(+x: Rational, +y: Rational, +z: Rational, xy: Rational.Eq(x, y), yz: Rational.Eq(y, z)) -> Rational.Eq(x, z):
  Rational.eq_transitive_bounds(x, y, z, Rational.eq_both_le(x, y, xy), Rational.eq_both_le(y, z, yz))

def Rational.le_replace_bounds(+x: Rational, +x_replacement: Rational, +y: Rational, +y_replacement: Rational,
  x_bounds: Rational.Le(x, x_replacement) & Rational.Le(x_replacement, x),
  y_bounds: Rational.Le(y, y_replacement) & Rational.Le(y_replacement, y),
  xy: Rational.Le(x, y)) -> Rational.Le(x_replacement, y_replacement):
  (x_forward, x_backward) = x_bounds
  (y_forward, y_backward) = y_bounds
  Rational.le_transitive(x_replacement, x, y_replacement, x_backward,
    Rational.le_transitive(x, y, y_replacement, xy, y_forward))

def Rational.le_replace(+x: Rational, +x_replacement: Rational, +y: Rational, +y_replacement: Rational,
  x_equal: Rational.Eq(x, x_replacement),
  y_equal: Rational.Eq(y, y_replacement),
  xy: Rational.Le(x, y)) -> Rational.Le(x_replacement, y_replacement):
  Rational.le_replace_bounds(x, x_replacement, y, y_replacement,
    Rational.eq_both_le(x, x_replacement, x_equal),
    Rational.eq_both_le(y, y_replacement, y_equal), xy)

def Rational.le_add_right_core(
  +xp: Nat, +xn: Nat, +xd: Nat,
  +yp: Nat, +yn: Nat, +yd: Nat,
  +zp: Nat, +zn: Nat, +zd: Nat,
  xy: N.Natural.Le(
    Nat.add(Nat.mul(xp, 1n+yd), Nat.mul(yn, 1n+xd)),
    Nat.add(Nat.mul(yp, 1n+xd), Nat.mul(xn, 1n+yd)))) ->
  Rational.Le(
    Rational.add(Fraction{xp, xn, xd}, Fraction{zp, zn, zd}),
    Rational.add(Fraction{yp, yn, yd}, Fraction{zp, zn, zd})):
  +dx: Nat = 1n+xd
  +dy: Nat = 1n+yd
  +dz: Nat = 1n+zd
  +dxz: Nat = 1n+Rational.denominator_product(xd, zd)
  +dyz: Nat = 1n+Rational.denominator_product(yd, zd)
  +pxz: Nat = Nat.add(Nat.mul(xp, dz), Nat.mul(zp, dx))
  +nxz: Nat = Nat.add(Nat.mul(xn, dz), Nat.mul(zn, dx))
  +pyz: Nat = Nat.add(Nat.mul(yp, dz), Nat.mul(zp, dy))
  +nyz: Nat = Nat.add(Nat.mul(yn, dz), Nat.mul(zn, dy))
  +ideal_left: Nat = Nat.add(Nat.mul(pxz, Nat.mul(dy, dz)), Nat.mul(nyz, Nat.mul(dx, dz)))
  +ideal_right: Nat = Nat.add(Nat.mul(pyz, Nat.mul(dx, dz)), Nat.mul(nxz, Nat.mul(dy, dz)))
  +actual_left: Nat = Nat.add(Nat.mul(pxz, dyz), Nat.mul(nyz, dxz))
  +actual_right: Nat = Nat.add(Nat.mul(pyz, dxz), Nat.mul(nxz, dyz))
  N.Natural.le_congruent(ideal_left, ideal_right, actual_left, actual_right,
    N.Natural.cross_shift_monotone(xp, yn, dx, dy, yp, xn, zp, zn, dz, xy),
    N.Natural.eq_add_congruent(
      Nat.mul(pxz, Nat.mul(dy, dz)), Nat.mul(nyz, Nat.mul(dx, dz)),
      Nat.mul(pxz, dyz), Nat.mul(nyz, dxz),
      Equal.cong(Nat, Nat, z => Nat.mul(pxz, z), Nat.mul(dy, dz), dyz,
        Equal.sym(Nat, dyz, Nat.mul(dy, dz), Rational.denominator_product_spec(yd, zd))),
      Equal.cong(Nat, Nat, z => Nat.mul(nyz, z), Nat.mul(dx, dz), dxz,
        Equal.sym(Nat, dxz, Nat.mul(dx, dz), Rational.denominator_product_spec(xd, zd)))),
    N.Natural.eq_add_congruent(
      Nat.mul(pyz, Nat.mul(dx, dz)), Nat.mul(nxz, Nat.mul(dy, dz)),
      Nat.mul(pyz, dxz), Nat.mul(nxz, dyz),
      Equal.cong(Nat, Nat, z => Nat.mul(pyz, z), Nat.mul(dx, dz), dxz,
        Equal.sym(Nat, dxz, Nat.mul(dx, dz), Rational.denominator_product_spec(xd, zd))),
      Equal.cong(Nat, Nat, z => Nat.mul(nxz, z), Nat.mul(dy, dz), dyz,
        Equal.sym(Nat, dyz, Nat.mul(dy, dz), Rational.denominator_product_spec(yd, zd)))))

def Rational.le_add_right(+x: Rational, +y: Rational, +z: Rational, xy: Rational.Le(x, y)) -> Rational.Le(Rational.add(x, z), Rational.add(y, z)):
  match x y z:
    case Fraction{xp, xn, xd} Fraction{yp, yn, yd} Fraction{zp, zn, zd}:
      Rational.le_add_right_core(xp, xn, xd, yp, yn, yd, zp, zn, zd, xy)

def Rational.le_structural_congruent(+a: Rational, +b: Rational, +c: Rational, +d: Rational,
  proof: Rational.Le(a, b), ac: {a == c : Rational}, bd: {b == d : Rational}) -> Rational.Le(c, d):
  %ac : Rational.Le(_, d)
  %bd : Rational.Le(a, _)
  proof

def Rational.le_add_left(+x: Rational, +y: Rational, +z: Rational, xy: Rational.Le(x, y)) -> Rational.Le(Rational.add(z, x), Rational.add(z, y)):
  Rational.le_structural_congruent(
    Rational.add(x, z), Rational.add(y, z), Rational.add(z, x), Rational.add(z, y),
    Rational.le_add_right(x, y, z, xy),
    Rational.add_commutative(x, z), Rational.add_commutative(y, z))

def Rational.eq_add_right_bounds(+x: Rational, +y: Rational, +z: Rational,
  bounds: Rational.Le(x, y) & Rational.Le(y, x)) -> Rational.Eq(Rational.add(x, z), Rational.add(y, z)):
  (forward, backward) = bounds
  Rational.le_antisymmetric(Rational.add(x, z), Rational.add(y, z),
    Rational.le_add_right(x, y, z, forward),
    Rational.le_add_right(y, x, z, backward))

def Rational.eq_add_right(+x: Rational, +y: Rational, +z: Rational, equality: Rational.Eq(x, y)) -> Rational.Eq(Rational.add(x, z), Rational.add(y, z)):
  Rational.eq_add_right_bounds(x, y, z, Rational.eq_both_le(x, y, equality))

def Rational.eq_structural_congruent(+a: Rational, +b: Rational, +c: Rational, +d: Rational,
  proof: Rational.Eq(a, b), ac: {a == c : Rational}, bd: {b == d : Rational}) -> Rational.Eq(c, d):
  %ac : Rational.Eq(_, d)
  %bd : Rational.Eq(a, _)
  proof

def Rational.eq_add_left(+x: Rational, +y: Rational, +z: Rational, equality: Rational.Eq(x, y)) -> Rational.Eq(Rational.add(z, x), Rational.add(z, y)):
  Rational.eq_structural_congruent(
    Rational.add(x, z), Rational.add(y, z), Rational.add(z, x), Rational.add(z, y),
    Rational.eq_add_right(x, y, z, equality),
    Rational.add_commutative(x, z), Rational.add_commutative(y, z))

def Rational.eq_add_both(+x: Rational, +x_replacement: Rational, +y: Rational, +y_replacement: Rational,
  x_equal: Rational.Eq(x, x_replacement), y_equal: Rational.Eq(y, y_replacement)) ->
  Rational.Eq(Rational.add(x, y), Rational.add(x_replacement, y_replacement)):
  Rational.eq_transitive(
    Rational.add(x, y), Rational.add(x_replacement, y), Rational.add(x_replacement, y_replacement),
    Rational.eq_add_right(x, x_replacement, y, x_equal),
    Rational.eq_add_left(y, y_replacement, x_replacement, y_equal))

def Rational.two_power_predecessor(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+Nat.double(Rational.two_power_predecessor(p))

def Rational.dyadic(n: Nat) -> Rational:
  Fraction{1n, 0n, Rational.two_power_predecessor(n)}

def Rational.dyadic_nonnegative(n: Nat) -> Rational.Le(Rational.zero(), Rational.dyadic(n)):
  N.Natural.zero_le(1n)
