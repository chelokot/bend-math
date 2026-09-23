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

def Rational.denominator_predecessor(x: Rational) -> Nat:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      denominator_predecessor

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

def Rational.cross_denominator_to_product(+p: Nat, +q: Nat, +a: Nat, +b: Nat, +z: Nat) ->
  {Nat.add(Nat.mul(p, 1n+Rational.denominator_product(a, z)), Nat.mul(q, 1n+Rational.denominator_product(b, z))) ==
   Nat.add(Nat.mul(p, Nat.mul(1n+a, 1n+z)), Nat.mul(q, Nat.mul(1n+b, 1n+z))) : Nat}:
  N.Natural.eq_add_congruent(
    Nat.mul(p, 1n+Rational.denominator_product(a, z)),
    Nat.mul(q, 1n+Rational.denominator_product(b, z)),
    Nat.mul(p, Nat.mul(1n+a, 1n+z)),
    Nat.mul(q, Nat.mul(1n+b, 1n+z)),
    Equal.cong(Nat, Nat, v => Nat.mul(p, v),
      1n+Rational.denominator_product(a, z), Nat.mul(1n+a, 1n+z),
      Rational.denominator_product_spec(a, z)),
    Equal.cong(Nat, Nat, v => Nat.mul(q, v),
      1n+Rational.denominator_product(b, z), Nat.mul(1n+b, 1n+z),
      Rational.denominator_product_spec(b, z)))

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

def Rational.add_structural_congruent(+a: Rational, +b: Rational, +c: Rational, +d: Rational,
  ac: {a == c : Rational}, bd: {b == d : Rational}) -> {Rational.add(a, b) == Rational.add(c, d) : Rational}:
  Equal.trans(Rational,
    Rational.add(a, b), Rational.add(c, b), Rational.add(c, d),
    Equal.cong(Rational, Rational, z => Rational.add(z, b), a, c, ac),
    Equal.cong(Rational, Rational, z => Rational.add(c, z), b, d, bd))

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

def Rational.add_swap(+a: Rational, +b: Rational, +c: Rational) ->
  {Rational.add(a, Rational.add(b, c)) == Rational.add(b, Rational.add(a, c)) : Rational}:
  Equal.trans(Rational,
    Rational.add(a, Rational.add(b, c)),
    Rational.add(Rational.add(a, b), c),
    Rational.add(b, Rational.add(a, c)),
    Equal.sym(Rational,
      Rational.add(Rational.add(a, b), c),
      Rational.add(a, Rational.add(b, c)),
      Rational.add_associative(a, b, c)),
    Equal.trans(Rational,
      Rational.add(Rational.add(a, b), c),
      Rational.add(Rational.add(b, a), c),
      Rational.add(b, Rational.add(a, c)),
      Equal.cong(Rational, Rational, z => Rational.add(z, c),
        Rational.add(a, b), Rational.add(b, a), Rational.add_commutative(a, b)),
      Rational.add_associative(b, a, c)))

def Rational.add_middle_commute(+a: Rational, +b: Rational, +c: Rational, +d: Rational) ->
  {Rational.add(Rational.add(a, b), Rational.add(c, d)) ==
   Rational.add(Rational.add(a, c), Rational.add(b, d)) : Rational}:
  Equal.trans(Rational,
    Rational.add(Rational.add(a, b), Rational.add(c, d)),
    Rational.add(a, Rational.add(b, Rational.add(c, d))),
    Rational.add(Rational.add(a, c), Rational.add(b, d)),
    Rational.add_associative(a, b, Rational.add(c, d)),
    Equal.trans(Rational,
      Rational.add(a, Rational.add(b, Rational.add(c, d))),
      Rational.add(a, Rational.add(c, Rational.add(b, d))),
      Rational.add(Rational.add(a, c), Rational.add(b, d)),
      Equal.cong(Rational, Rational, z => Rational.add(a, z),
        Rational.add(b, Rational.add(c, d)), Rational.add(c, Rational.add(b, d)),
        Rational.add_swap(b, c, d)),
      Equal.sym(Rational,
        Rational.add(Rational.add(a, c), Rational.add(b, d)),
        Rational.add(a, Rational.add(c, Rational.add(b, d))),
        Rational.add_associative(a, c, Rational.add(b, d)))))

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

def Rational.scale(x: Rational, +factor_predecessor: Nat) -> Rational:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      Fraction{
        Nat.mul(positive, 1n+factor_predecessor),
        Nat.mul(negative, 1n+factor_predecessor),
        Rational.denominator_product(denominator_predecessor, factor_predecessor)
      }

def Rational.inverse_from_difference(denominator_predecessor: Nat, difference: Z.Integer) -> Rational:
  match difference:
    case Z.ZPos{magnitude}:
      match magnitude:
        case 0n:
          Rational.zero()
        case 1n+predecessor:
          Fraction{1n+denominator_predecessor, 0n, predecessor}
    case Z.ZNeg{predecessor}:
      Fraction{0n, 1n+denominator_predecessor, predecessor}

def Rational.inverse(x: Rational) -> Rational:
  match x:
    case Fraction{positive, negative, denominator_predecessor}:
      Rational.inverse_from_difference(denominator_predecessor, Z.Integer.subtract_naturals(positive, negative))

def Rational.mul_neg_right(a: Rational, b: Rational) -> {Rational.mul(a, Rational.neg(b)) == Rational.neg(Rational.mul(a, b)) : Rational}:
  match a b:
    case Fraction{ap, an, ad} Fraction{bp, bn, bd}:
      {==}

def Rational.mul_pure_positive_shape(+p: Nat, +n: Nat, +d: Nat, +k: Nat) ->
  {Rational.mul(Fraction{p, n, d}, Fraction{1n+d, 0n, k}) ==
   Fraction{Nat.mul(p, 1n+d), Nat.mul(n, 1n+d), Rational.denominator_product(d, k)} : Rational}:
  +denominator: Nat = 1n+d
  Rational.fraction_congruent(
    Nat.add(Nat.mul(p, denominator), Nat.mul(n, 0n)),
    Nat.add(Nat.mul(p, 0n), Nat.mul(n, denominator)),
    Rational.denominator_product(d, k),
    Nat.mul(p, denominator), Nat.mul(n, denominator), Rational.denominator_product(d, k),
    Equal.trans(Nat,
      Nat.add(Nat.mul(p, denominator), Nat.mul(n, 0n)),
      Nat.add(Nat.mul(p, denominator), 0n),
      Nat.mul(p, denominator),
      N.Natural.eq_add_congruent(
        Nat.mul(p, denominator), Nat.mul(n, 0n), Nat.mul(p, denominator), 0n,
        {==}, N.Natural.mul_zero(n)),
      N.Natural.add_zero(Nat.mul(p, denominator))),
    N.Natural.eq_add_congruent(
      Nat.mul(p, 0n), Nat.mul(n, denominator), 0n, Nat.mul(n, denominator),
      N.Natural.mul_zero(p), {==}),
    {==})

def Rational.mul_pure_negative_shape(+p: Nat, +n: Nat, +d: Nat, +k: Nat) ->
  {Rational.mul(Fraction{p, n, d}, Fraction{0n, 1n+d, k}) ==
   Fraction{Nat.mul(n, 1n+d), Nat.mul(p, 1n+d), Rational.denominator_product(d, k)} : Rational}:
  +x: Rational = Fraction{p, n, d}
  +positive_inverse: Rational = Fraction{1n+d, 0n, k}
  +positive_product: Rational = Fraction{Nat.mul(p, 1n+d), Nat.mul(n, 1n+d), Rational.denominator_product(d, k)}
  Equal.trans(Rational,
    Rational.mul(x, Rational.neg(positive_inverse)),
    Rational.neg(Rational.mul(x, positive_inverse)),
    Rational.neg(positive_product),
    Rational.mul_neg_right(x, positive_inverse),
    Equal.cong(Rational, Rational, Rational.neg,
      Rational.mul(x, positive_inverse), positive_product,
      Rational.mul_pure_positive_shape(p, n, d, k)))

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

def Rational.mul_swap_associative(+a: Rational, +b: Rational, +c: Rational) ->
  {Rational.mul(a, Rational.mul(b, c)) == Rational.mul(Rational.mul(b, a), c) : Rational}:
  Equal.trans(Rational,
    Rational.mul(a, Rational.mul(b, c)),
    Rational.mul(Rational.mul(a, b), c),
    Rational.mul(Rational.mul(b, a), c),
    Equal.sym(Rational,
      Rational.mul(Rational.mul(a, b), c), Rational.mul(a, Rational.mul(b, c)),
      Rational.mul_associative(a, b, c)),
    Equal.cong(Rational, Rational, z => Rational.mul(z, c),
      Rational.mul(a, b), Rational.mul(b, a),
      Rational.mul_commutative(a, b)))

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

def Rational.eq_from_structural(+a: Rational, +b: Rational, proof: {a == b : Rational}) -> Rational.Eq(a, b):
  %proof : Rational.Eq(a, _)
  {==}

def Rational.eq_one_of_positive_gap(+p: Nat, +n: Nat, +d: Nat, +k: Nat,
  proof: {p == Nat.add(n, 1n+k) : Nat}) ->
  Rational.Eq(
    Fraction{Nat.mul(p, 1n+d), Nat.mul(n, 1n+d), Rational.denominator_product(d, k)},
    Rational.one()):
  +denominator: Nat = 1n+d
  +gap: Nat = 1n+k
  +product_denominator: Nat = 1n+Rational.denominator_product(d, k)
  +positive_product: Nat = Nat.mul(p, denominator)
  +negative_product: Nat = Nat.mul(n, denominator)
  +left: Nat = Nat.add(Nat.mul(positive_product, 1n), 0n)
  +right: Nat = Nat.add(Nat.mul(1n, product_denominator), Nat.mul(negative_product, 1n))
  +balanced: Nat = Nat.add(Nat.mul(denominator, gap), negative_product)
  +denominator_sum: Nat = Nat.add(product_denominator, negative_product)
  Equal.trans(Nat,
    left, positive_product, right,
    Equal.trans(Nat,
      left, Nat.mul(positive_product, 1n), positive_product,
      N.Natural.add_zero(Nat.mul(positive_product, 1n)),
      N.Natural.mul_one(positive_product)),
    Equal.trans(Nat,
      positive_product, balanced, right,
      N.Natural.mul_gap_one(p, n, denominator, gap, proof),
      Equal.trans(Nat,
        balanced, denominator_sum, right,
        N.Natural.eq_add_congruent(
          Nat.mul(denominator, gap), negative_product,
          product_denominator, negative_product,
          Equal.sym(Nat, product_denominator, Nat.mul(denominator, gap),
            Rational.denominator_product_spec(d, k)),
          {==}),
        Equal.sym(Nat, right, denominator_sum,
          N.Natural.eq_add_congruent(
            Nat.mul(1n, product_denominator), Nat.mul(negative_product, 1n),
            product_denominator, negative_product,
            N.Natural.one_mul(product_denominator),
            N.Natural.mul_one(negative_product))))))

def Rational.scale_preserves_eq(x: Rational, +factor_predecessor: Nat) -> Rational.Eq(x, Rational.scale(x, factor_predecessor)):
  match x:
    case Fraction{+p, +n, +d}:
      +denominator: Nat = 1n+d
      +factor: Nat = 1n+factor_predecessor
      +scaled_denominator: Nat = 1n+Rational.denominator_product(d, factor_predecessor)
      +left: Nat = Nat.add(Nat.mul(p, scaled_denominator), Nat.mul(Nat.mul(n, factor), denominator))
      +right: Nat = Nat.add(Nat.mul(Nat.mul(p, factor), denominator), Nat.mul(n, scaled_denominator))
      Equal.trans(Nat,
        left,
        Nat.add(Nat.mul(p, Nat.mul(denominator, factor)), Nat.mul(Nat.mul(n, factor), denominator)),
        right,
        N.Natural.eq_add_congruent(
          Nat.mul(p, scaled_denominator), Nat.mul(Nat.mul(n, factor), denominator),
          Nat.mul(p, Nat.mul(denominator, factor)), Nat.mul(Nat.mul(n, factor), denominator),
          Equal.cong(Nat, Nat, z => Nat.mul(p, z),
            scaled_denominator, Nat.mul(denominator, factor),
            Rational.denominator_product_spec(d, factor_predecessor)),
          {==}),
        Equal.trans(Nat,
          Nat.add(Nat.mul(p, Nat.mul(denominator, factor)), Nat.mul(Nat.mul(n, factor), denominator)),
          Nat.add(Nat.mul(Nat.mul(p, factor), denominator), Nat.mul(n, Nat.mul(denominator, factor))),
          right,
          N.Natural.eq_add_congruent(
            Nat.mul(p, Nat.mul(denominator, factor)), Nat.mul(Nat.mul(n, factor), denominator),
            Nat.mul(Nat.mul(p, factor), denominator), Nat.mul(n, Nat.mul(denominator, factor)),
            N.Natural.mul_inner_swap(p, denominator, factor),
            Equal.sym(Nat,
              Nat.mul(n, Nat.mul(denominator, factor)),
              Nat.mul(Nat.mul(n, factor), denominator),
              N.Natural.mul_inner_swap(n, denominator, factor))),
          N.Natural.eq_add_congruent(
            Nat.mul(Nat.mul(p, factor), denominator), Nat.mul(n, Nat.mul(denominator, factor)),
            Nat.mul(Nat.mul(p, factor), denominator), Nat.mul(n, scaled_denominator),
            {==},
            Equal.cong(Nat, Nat, z => Nat.mul(n, z),
              Nat.mul(denominator, factor), scaled_denominator,
              Equal.sym(Nat, scaled_denominator, Nat.mul(denominator, factor),
                Rational.denominator_product_spec(d, factor_predecessor))))))

def Rational.distributive_scaled_numerator(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat,
  +ad: Nat, +bd: Nat, +cd: Nat) ->
  {Nat.mul(Nat.add(
     Nat.mul(a, Nat.add(Nat.mul(c, 1n+cd), Nat.mul(e, 1n+bd))),
     Nat.mul(b, Nat.add(Nat.mul(d, 1n+cd), Nat.mul(f, 1n+bd)))), 1n+ad) ==
   Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), 1n+Rational.denominator_product(ad, cd)),
     Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, f)), 1n+Rational.denominator_product(ad, bd))) : Nat}:
  +da: Nat = 1n+ad
  +db: Nat = 1n+bd
  +dc: Nat = 1n+cd
  +first: Nat = Nat.add(Nat.mul(a, c), Nat.mul(b, d))
  +second: Nat = Nat.add(Nat.mul(a, e), Nat.mul(b, f))
  +left: Nat = Nat.mul(Nat.add(
    Nat.mul(a, Nat.add(Nat.mul(c, dc), Nat.mul(e, db))),
    Nat.mul(b, Nat.add(Nat.mul(d, dc), Nat.mul(f, db)))), da)
  +middle: Nat = Nat.add(Nat.mul(first, Nat.mul(da, dc)), Nat.mul(second, Nat.mul(da, db)))
  +right: Nat = Nat.add(
    Nat.mul(first, 1n+Rational.denominator_product(ad, cd)),
    Nat.mul(second, 1n+Rational.denominator_product(ad, bd)))
  Equal.trans(Nat,
    left, middle, right,
    N.Natural.matrix_distributive_scaled(a, b, c, d, e, f, dc, db, da),
    N.Natural.eq_add_congruent(
      Nat.mul(first, Nat.mul(da, dc)), Nat.mul(second, Nat.mul(da, db)),
      Nat.mul(first, 1n+Rational.denominator_product(ad, cd)),
      Nat.mul(second, 1n+Rational.denominator_product(ad, bd)),
      Equal.cong(Nat, Nat, z => Nat.mul(first, z),
        Nat.mul(da, dc), 1n+Rational.denominator_product(ad, cd),
        Equal.sym(Nat,
          1n+Rational.denominator_product(ad, cd), Nat.mul(da, dc),
          Rational.denominator_product_spec(ad, cd))),
      Equal.cong(Nat, Nat, z => Nat.mul(second, z),
        Nat.mul(da, db), 1n+Rational.denominator_product(ad, bd),
        Equal.sym(Nat,
          1n+Rational.denominator_product(ad, bd), Nat.mul(da, db),
          Rational.denominator_product_spec(ad, bd)))))

def Rational.denominator_distributive_scale(+ad: Nat, +bd: Nat, +cd: Nat) ->
  {Rational.denominator_product(Rational.denominator_product(ad, Rational.denominator_product(bd, cd)), ad) ==
   Rational.denominator_product(Rational.denominator_product(ad, bd), Rational.denominator_product(ad, cd)) : Nat}:
  +da: Nat = 1n+ad
  +db: Nat = 1n+bd
  +dc: Nat = 1n+cd
  +dab: Nat = Rational.denominator_product(ad, bd)
  +dac: Nat = Rational.denominator_product(ad, cd)
  +dbc: Nat = Rational.denominator_product(bd, cd)
  +dabc: Nat = Rational.denominator_product(ad, dbc)
  +left_predecessor: Nat = Rational.denominator_product(dabc, ad)
  +right_predecessor: Nat = Rational.denominator_product(dab, dac)
  +first: Nat = Nat.mul(1n+dabc, da)
  +second: Nat = Nat.mul(Nat.mul(da, 1n+dbc), da)
  +third: Nat = Nat.mul(Nat.mul(da, Nat.mul(db, dc)), da)
  +fourth: Nat = Nat.mul(Nat.mul(da, da), Nat.mul(db, dc))
  +fifth: Nat = Nat.mul(Nat.mul(da, db), Nat.mul(da, dc))
  +sixth: Nat = Nat.mul(1n+dab, 1n+dac)
  N.Natural.successor_injective(left_predecessor, right_predecessor,
    Equal.trans(Nat,
      1n+left_predecessor, first, 1n+right_predecessor,
      Rational.denominator_product_spec(dabc, ad),
      Equal.trans(Nat,
        first, second, 1n+right_predecessor,
        Equal.cong(Nat, Nat, z => Nat.mul(z, da),
          1n+dabc, Nat.mul(da, 1n+dbc),
          Rational.denominator_product_spec(ad, dbc)),
        Equal.trans(Nat,
          second, third, 1n+right_predecessor,
          Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(da, z), da),
            1n+dbc, Nat.mul(db, dc),
            Rational.denominator_product_spec(bd, cd)),
          Equal.trans(Nat,
            third, fourth, 1n+right_predecessor,
            N.Natural.mul_last_swap(da, Nat.mul(db, dc), da),
            Equal.trans(Nat,
              fourth, fifth, 1n+right_predecessor,
              Equal.sym(Nat, fifth, fourth,
                N.Natural.mul_four_middle_commute(da, db, da, dc)),
              Equal.trans(Nat,
                fifth, sixth, 1n+right_predecessor,
                N.Natural.eq_mul_congruent(
                  Nat.mul(da, db), Nat.mul(da, dc), 1n+dab, 1n+dac,
                  Equal.sym(Nat, 1n+dab, Nat.mul(da, db), Rational.denominator_product_spec(ad, bd)),
                  Equal.sym(Nat, 1n+dac, Nat.mul(da, dc), Rational.denominator_product_spec(ad, cd))),
                Equal.sym(Nat,
                  1n+right_predecessor, sixth,
                  Rational.denominator_product_spec(dab, dac)))))))))

def Rational.distributive_scaled_structural(a: Rational, b: Rational, c: Rational) ->
  {Rational.scale(Rational.mul(a, Rational.add(b, c)), Rational.denominator_predecessor(a)) ==
   Rational.add(Rational.mul(a, b), Rational.mul(a, c)) : Rational}:
  match a b c:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd} Fraction{+cp, +cn, +cd}:
      Rational.fraction_congruent(
        Nat.mul(Nat.add(
          Nat.mul(ap, Nat.add(Nat.mul(bp, 1n+cd), Nat.mul(cp, 1n+bd))),
          Nat.mul(an, Nat.add(Nat.mul(bn, 1n+cd), Nat.mul(cn, 1n+bd)))), 1n+ad),
        Nat.mul(Nat.add(
          Nat.mul(ap, Nat.add(Nat.mul(bn, 1n+cd), Nat.mul(cn, 1n+bd))),
          Nat.mul(an, Nat.add(Nat.mul(bp, 1n+cd), Nat.mul(cp, 1n+bd)))), 1n+ad),
        Rational.denominator_product(Rational.denominator_product(ad, Rational.denominator_product(bd, cd)), ad),
        Nat.add(
          Nat.mul(Nat.add(Nat.mul(ap, bp), Nat.mul(an, bn)), 1n+Rational.denominator_product(ad, cd)),
          Nat.mul(Nat.add(Nat.mul(ap, cp), Nat.mul(an, cn)), 1n+Rational.denominator_product(ad, bd))),
        Nat.add(
          Nat.mul(Nat.add(Nat.mul(ap, bn), Nat.mul(an, bp)), 1n+Rational.denominator_product(ad, cd)),
          Nat.mul(Nat.add(Nat.mul(ap, cn), Nat.mul(an, cp)), 1n+Rational.denominator_product(ad, bd))),
        Rational.denominator_product(Rational.denominator_product(ad, bd), Rational.denominator_product(ad, cd)),
        Rational.distributive_scaled_numerator(ap, an, bp, bn, cp, cn, ad, bd, cd),
        Rational.distributive_scaled_numerator(ap, an, bn, bp, cn, cp, ad, bd, cd),
        Rational.denominator_distributive_scale(ad, bd, cd))

def Rational.eq_zero_if_balanced(+positive: Nat, +negative: Nat, +denominator_predecessor: Nat, proof: {positive == negative : Nat}) -> Rational.Eq(Fraction{positive, negative, denominator_predecessor}, Rational.zero()):
  Equal.trans(Nat,
    Nat.add(Nat.mul(positive, 1n), 0n),
    Nat.add(0n, Nat.mul(positive, 1n)),
    Nat.add(0n, Nat.mul(negative, 1n)),
    N.Natural.add_commutative(Nat.mul(positive, 1n), 0n),
    Equal.cong(Nat, Nat, z => Nat.add(0n, Nat.mul(z, 1n)), positive, negative, proof))

def Rational.eq_zero_implies_balanced(+positive: Nat, +negative: Nat, +denominator_predecessor: Nat,
  proof: Rational.Eq(Fraction{positive, negative, denominator_predecessor}, Rational.zero())) ->
  {positive == negative : Nat}:
  +left: Nat = Nat.add(Nat.mul(positive, 1n), 0n)
  +right: Nat = Nat.add(0n, Nat.mul(negative, 1n))
  Equal.trans(Nat,
    positive, Nat.mul(positive, 1n), negative,
    Equal.sym(Nat, Nat.mul(positive, 1n), positive, N.Natural.mul_one(positive)),
    Equal.trans(Nat,
      Nat.mul(positive, 1n), left, negative,
      Equal.sym(Nat, left, Nat.mul(positive, 1n), N.Natural.add_zero(Nat.mul(positive, 1n))),
      Equal.trans(Nat,
        left, right, negative,
        proof,
        N.Natural.mul_one(negative))))

def Rational.inverse_zero_if_eq(x: Rational, proof: Rational.Eq(x, Rational.zero())) -> Rational.Eq(Rational.inverse(x), Rational.zero()):
  match x:
    case Fraction{+positive, +negative, +denominator_predecessor}:
      +balanced: {positive == negative : Nat} = Rational.eq_zero_implies_balanced(positive, negative, denominator_predecessor, proof)
      +difference_equal: {Z.Integer.subtract_naturals(positive, negative) == Z.Integer.zero() : Z.Integer} =
        Equal.trans(Z.Integer,
          Z.Integer.subtract_naturals(positive, negative),
          Z.Integer.subtract_naturals(negative, negative),
          Z.Integer.zero(),
          Equal.cong(Nat, Z.Integer, z => Z.Integer.subtract_naturals(z, negative),
            positive, negative, balanced),
          Z.Integer.subtract_same(negative))
      Rational.eq_from_structural(
        Rational.inverse(Fraction{positive, negative, denominator_predecessor}), Rational.zero(),
        Equal.cong(Z.Integer, Rational,
          z => Rational.inverse_from_difference(denominator_predecessor, z),
          Z.Integer.subtract_naturals(positive, negative), Z.Integer.zero(),
          difference_equal))

def Rational.zero_or_nonzero_by_difference(+p: Nat, +n: Nat, +d: Nat, difference: Z.Integer,
  specification: Z.Integer.SubtractSpec(p, n, difference)) ->
  Or(Rational.Eq(Fraction{p, n, d}, Rational.zero()),
     Rational.Eq(Fraction{p, n, d}, Rational.zero()) -> Empty):
  match difference:
    case Z.ZPos{magnitude}:
      match magnitude:
        case 0n:
          Inl{Rational.eq_zero_if_balanced(p, n, d,
            Equal.trans(Nat,
              p, Nat.add(n, 0n), n,
              specification, N.Natural.add_zero(n)))}
        case 1n+k:
          Inr{contradiction => N.Natural.positive_gap_not_equal(p, n, k,
            specification,
            Rational.eq_zero_implies_balanced(p, n, d, contradiction))}
    case Z.ZNeg{predecessor}:
      Inr{contradiction => N.Natural.positive_gap_not_equal(n, p, predecessor,
        specification,
        Equal.sym(Nat, p, n,
          Rational.eq_zero_implies_balanced(p, n, d, contradiction)))}

def Rational.zero_or_nonzero(x: Rational) -> Or(Rational.Eq(x, Rational.zero()), Rational.Eq(x, Rational.zero()) -> Empty):
  match x:
    case Fraction{+p, +n, +d}:
      Rational.zero_or_nonzero_by_difference(p, n, d,
        Z.Integer.subtract_naturals(p, n),
        Z.Integer.subtract_spec(p, n))

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

def Rational.nonnegative_left_cross(+p: Nat, +n: Nat, +d: Nat) ->
  {Rational.left_cross(Rational.zero(), Fraction{p, n, d}) == n : Nat}:
  N.Natural.mul_one(n)

def Rational.nonnegative_right_cross(+p: Nat, +n: Nat, +d: Nat) ->
  {Rational.right_cross(Rational.zero(), Fraction{p, n, d}) == p : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.mul(p, 1n), 0n), Nat.mul(p, 1n), p,
    N.Natural.add_zero(Nat.mul(p, 1n)), N.Natural.mul_one(p))

def Rational.nonnegative_from_nat(+p: Nat, +n: Nat, +d: Nat, proof: N.Natural.Le(n, p)) ->
  Rational.Le(Rational.zero(), Fraction{p, n, d}):
  N.Natural.le_congruent(n, p,
    Rational.left_cross(Rational.zero(), Fraction{p, n, d}),
    Rational.right_cross(Rational.zero(), Fraction{p, n, d}),
    proof,
    Equal.sym(Nat,
      Rational.left_cross(Rational.zero(), Fraction{p, n, d}), n,
      Rational.nonnegative_left_cross(p, n, d)),
    Equal.sym(Nat,
      Rational.right_cross(Rational.zero(), Fraction{p, n, d}), p,
      Rational.nonnegative_right_cross(p, n, d)))

def Rational.nonnegative_to_nat(+p: Nat, +n: Nat, +d: Nat,
  proof: Rational.Le(Rational.zero(), Fraction{p, n, d})) -> N.Natural.Le(n, p):
  N.Natural.le_congruent(
    Rational.left_cross(Rational.zero(), Fraction{p, n, d}),
    Rational.right_cross(Rational.zero(), Fraction{p, n, d}),
    n, p, proof,
    Rational.nonnegative_left_cross(p, n, d),
    Rational.nonnegative_right_cross(p, n, d))

def Rational.mul_nonnegative(+x: Rational, +y: Rational,
  x_nonnegative: Rational.Le(Rational.zero(), x),
  y_nonnegative: Rational.Le(Rational.zero(), y)) ->
  Rational.Le(Rational.zero(), Rational.mul(x, y)):
  match x y:
    case Fraction{+p, +n, +d} Fraction{+q, +m, +e}:
      Rational.nonnegative_from_nat(
        Nat.add(Nat.mul(p, q), Nat.mul(n, m)),
        Nat.add(Nat.mul(p, m), Nat.mul(n, q)),
        Rational.denominator_product(d, e),
        N.Natural.signed_mul_nonnegative(p, n, q, m,
          Rational.nonnegative_to_nat(p, n, d, x_nonnegative),
          Rational.nonnegative_to_nat(q, m, e, y_nonnegative)))

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

def Rational.le_add_both(+a: Rational, +b: Rational, +c: Rational, +d: Rational,
  ab: Rational.Le(a, b), cd: Rational.Le(c, d)) -> Rational.Le(Rational.add(a, c), Rational.add(b, d)):
  Rational.le_transitive(Rational.add(a, c), Rational.add(b, c), Rational.add(b, d),
    Rational.le_add_right(a, b, c, ab),
    Rational.le_add_left(c, d, b, cd))

def Rational.le_add_with_common_error(+a: Rational, +b: Rational, +c: Rational, +d: Rational, +error: Rational,
  ab: Rational.Le(a, Rational.add(b, error)),
  cd: Rational.Le(c, Rational.add(d, error))) ->
  Rational.Le(Rational.add(a, c), Rational.add(Rational.add(b, d), Rational.add(error, error))):
  Rational.le_structural_congruent(
    Rational.add(a, c),
    Rational.add(Rational.add(b, error), Rational.add(d, error)),
    Rational.add(a, c),
    Rational.add(Rational.add(b, d), Rational.add(error, error)),
    Rational.le_add_both(a, Rational.add(b, error), c, Rational.add(d, error), ab, cd),
    {==},
    Rational.add_middle_commute(b, error, d, error))

def Rational.close_add_same_errors(+a: Rational, +b: Rational, +c: Rational, +d: Rational,
  +left_error: Rational, +right_error: Rational,
  first: Rational.Close(a, b, left_error, right_error),
  second: Rational.Close(c, d, left_error, right_error)) ->
  Rational.Close(Rational.add(a, c), Rational.add(b, d),
    Rational.add(left_error, left_error), Rational.add(right_error, right_error)):
  (first_forward, first_backward) = first
  (second_forward, second_backward) = second
  +forward_error: Rational = Rational.add(left_error, right_error)
  +backward_error: Rational = Rational.add(right_error, left_error)
  (
    Rational.le_structural_congruent(
      Rational.add(a, c),
      Rational.add(Rational.add(b, d), Rational.add(forward_error, forward_error)),
      Rational.add(a, c),
      Rational.add(Rational.add(b, d),
        Rational.add(Rational.add(left_error, left_error), Rational.add(right_error, right_error))),
      Rational.le_add_with_common_error(a, b, c, d, forward_error,
        first_forward, second_forward),
      {==},
      Equal.cong(Rational, Rational, z => Rational.add(Rational.add(b, d), z),
        Rational.add(forward_error, forward_error),
        Rational.add(Rational.add(left_error, left_error), Rational.add(right_error, right_error)),
        Rational.add_middle_commute(left_error, right_error, left_error, right_error))),
    Rational.le_structural_congruent(
      Rational.add(b, d),
      Rational.add(Rational.add(a, c), Rational.add(backward_error, backward_error)),
      Rational.add(b, d),
      Rational.add(Rational.add(a, c),
        Rational.add(Rational.add(right_error, right_error), Rational.add(left_error, left_error))),
      Rational.le_add_with_common_error(b, a, d, c, backward_error,
        first_backward, second_backward),
      {==},
      Equal.cong(Rational, Rational, z => Rational.add(Rational.add(a, c), z),
        Rational.add(backward_error, backward_error),
        Rational.add(Rational.add(right_error, right_error), Rational.add(left_error, left_error)),
        Rational.add_middle_commute(right_error, left_error, right_error, left_error)))
  )

def Rational.add_nonnegative(+x: Rational, +y: Rational,
  x_nonnegative: Rational.Le(Rational.zero(), x),
  y_nonnegative: Rational.Le(Rational.zero(), y)) ->
  Rational.Le(Rational.zero(), Rational.add(x, y)):
  Rational.le_transitive(Rational.zero(), y, Rational.add(x, y),
    y_nonnegative,
    Rational.le_structural_congruent(
      Rational.add(Rational.zero(), y), Rational.add(x, y),
      y, Rational.add(x, y),
      Rational.le_add_right(Rational.zero(), x, y, x_nonnegative),
      Rational.zero_add(y), {==}))

def Rational.le_self_add_nonnegative(+x: Rational, +y: Rational,
  y_nonnegative: Rational.Le(Rational.zero(), y)) -> Rational.Le(x, Rational.add(x, y)):
  Rational.le_structural_congruent(
    Rational.add(x, Rational.zero()), Rational.add(x, y),
    x, Rational.add(x, y),
    Rational.le_add_left(Rational.zero(), y, x, y_nonnegative),
    Rational.add_zero(x), {==})

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

def Rational.close_replace_errors(+x: Rational, +y: Rational,
  +left_error: Rational, +right_error: Rational,
  +new_left_error: Rational, +new_right_error: Rational,
  proof: Rational.Close(x, y, left_error, right_error),
  forward_equality: Rational.Eq(Rational.add(left_error, right_error), Rational.add(new_left_error, new_right_error)),
  backward_equality: Rational.Eq(Rational.add(right_error, left_error), Rational.add(new_right_error, new_left_error))) ->
  Rational.Close(x, y, new_left_error, new_right_error):
  (forward, backward) = proof
  (
    Rational.le_replace(x, x,
      Rational.add(y, Rational.add(left_error, right_error)),
      Rational.add(y, Rational.add(new_left_error, new_right_error)),
      Rational.eq_reflexive(x),
      Rational.eq_add_left(
        Rational.add(left_error, right_error), Rational.add(new_left_error, new_right_error),
        y, forward_equality),
      forward),
    Rational.le_replace(y, y,
      Rational.add(x, Rational.add(right_error, left_error)),
      Rational.add(x, Rational.add(new_right_error, new_left_error)),
      Rational.eq_reflexive(y),
      Rational.eq_add_left(
        Rational.add(right_error, left_error), Rational.add(new_right_error, new_left_error),
        x, backward_equality),
      backward)
  )

def Rational.eq_mul_right_core(
  +xp: Nat, +xn: Nat, +xd: Nat,
  +yp: Nat, +yn: Nat, +yd: Nat,
  +zp: Nat, +zn: Nat, +zd: Nat,
  xy: {Nat.add(Nat.mul(xp, 1n+yd), Nat.mul(yn, 1n+xd)) ==
       Nat.add(Nat.mul(yp, 1n+xd), Nat.mul(xn, 1n+yd)) : Nat}) ->
  Rational.Eq(
    Rational.mul(Fraction{xp, xn, xd}, Fraction{zp, zn, zd}),
    Rational.mul(Fraction{yp, yn, yd}, Fraction{zp, zn, zd})):
  +dx: Nat = 1n+xd
  +dy: Nat = 1n+yd
  +dz: Nat = 1n+zd
  +pxz: Nat = Nat.add(Nat.mul(xp, zp), Nat.mul(xn, zn))
  +nxz: Nat = Nat.add(Nat.mul(xp, zn), Nat.mul(xn, zp))
  +pyz: Nat = Nat.add(Nat.mul(yp, zp), Nat.mul(yn, zn))
  +nyz: Nat = Nat.add(Nat.mul(yp, zn), Nat.mul(yn, zp))
  +actual_left: Nat = Nat.add(Nat.mul(pxz, 1n+Rational.denominator_product(yd, zd)), Nat.mul(nyz, 1n+Rational.denominator_product(xd, zd)))
  +actual_right: Nat = Nat.add(Nat.mul(pyz, 1n+Rational.denominator_product(xd, zd)), Nat.mul(nxz, 1n+Rational.denominator_product(yd, zd)))
  +ideal_left: Nat = Nat.add(Nat.mul(pxz, Nat.mul(dy, dz)), Nat.mul(nyz, Nat.mul(dx, dz)))
  +ideal_right: Nat = Nat.add(Nat.mul(pyz, Nat.mul(dx, dz)), Nat.mul(nxz, Nat.mul(dy, dz)))
  +inner_left: Nat = Nat.add(Nat.mul(pxz, dy), Nat.mul(nyz, dx))
  +inner_right: Nat = Nat.add(Nat.mul(pyz, dx), Nat.mul(nxz, dy))
  Equal.trans(Nat,
    actual_left, ideal_left, actual_right,
    Rational.cross_denominator_to_product(pxz, nyz, yd, xd, zd),
    Equal.trans(Nat,
      ideal_left, Nat.mul(inner_left, dz), actual_right,
      N.Natural.sum_mul_associative(pxz, dy, nyz, dx, dz),
      Equal.trans(Nat,
        Nat.mul(inner_left, dz), Nat.mul(inner_right, dz), actual_right,
        Equal.cong(Nat, Nat, v => Nat.mul(v, dz), inner_left, inner_right,
          N.Natural.cross_mul_respects_eq(xp, xn, yp, yn, dy, dx, zp, zn, xy)),
        Equal.trans(Nat,
          Nat.mul(inner_right, dz), ideal_right, actual_right,
          Equal.sym(Nat, ideal_right, Nat.mul(inner_right, dz),
            N.Natural.sum_mul_associative(pyz, dx, nxz, dy, dz)),
          Equal.sym(Nat, actual_right, ideal_right,
            Rational.cross_denominator_to_product(pyz, nxz, xd, yd, zd))))))

def Rational.eq_mul_right(+x: Rational, +y: Rational, +z: Rational, equality: Rational.Eq(x, y)) -> Rational.Eq(Rational.mul(x, z), Rational.mul(y, z)):
  match x y z:
    case Fraction{xp, xn, xd} Fraction{yp, yn, yd} Fraction{zp, zn, zd}:
      Rational.eq_mul_right_core(xp, xn, xd, yp, yn, yd, zp, zn, zd, equality)

def Rational.eq_mul_left(+x: Rational, +y: Rational, +z: Rational, equality: Rational.Eq(x, y)) -> Rational.Eq(Rational.mul(z, x), Rational.mul(z, y)):
  Rational.eq_structural_congruent(
    Rational.mul(x, z), Rational.mul(y, z), Rational.mul(z, x), Rational.mul(z, y),
    Rational.eq_mul_right(x, y, z, equality),
    Rational.mul_commutative(x, z), Rational.mul_commutative(y, z))

def Rational.eq_mul_both(+x: Rational, +x_replacement: Rational, +y: Rational, +y_replacement: Rational,
  x_equal: Rational.Eq(x, x_replacement), y_equal: Rational.Eq(y, y_replacement)) ->
  Rational.Eq(Rational.mul(x, y), Rational.mul(x_replacement, y_replacement)):
  Rational.eq_transitive(
    Rational.mul(x, y), Rational.mul(x_replacement, y), Rational.mul(x_replacement, y_replacement),
    Rational.eq_mul_right(x, x_replacement, y, x_equal),
    Rational.eq_mul_left(y, y_replacement, x_replacement, y_equal))

def Rational.inverse_positive_cancel(+p: Nat, +n: Nat, +d: Nat, +k: Nat,
  proof: {p == Nat.add(n, 1n+k) : Nat}) ->
  Rational.Eq(Rational.mul(Fraction{p, n, d}, Fraction{1n+d, 0n, k}), Rational.one()):
  +product: Rational = Rational.mul(Fraction{p, n, d}, Fraction{1n+d, 0n, k})
  +simplified: Rational = Fraction{Nat.mul(p, 1n+d), Nat.mul(n, 1n+d), Rational.denominator_product(d, k)}
  Rational.eq_structural_congruent(simplified, Rational.one(), product, Rational.one(),
    Rational.eq_one_of_positive_gap(p, n, d, k, proof),
    Equal.sym(Rational, product, simplified, Rational.mul_pure_positive_shape(p, n, d, k)),
    {==})

def Rational.inverse_negative_cancel(+p: Nat, +n: Nat, +d: Nat, +k: Nat,
  proof: {n == Nat.add(p, 1n+k) : Nat}) ->
  Rational.Eq(Rational.mul(Fraction{p, n, d}, Fraction{0n, 1n+d, k}), Rational.one()):
  +product: Rational = Rational.mul(Fraction{p, n, d}, Fraction{0n, 1n+d, k})
  +simplified: Rational = Fraction{Nat.mul(n, 1n+d), Nat.mul(p, 1n+d), Rational.denominator_product(d, k)}
  Rational.eq_structural_congruent(simplified, Rational.one(), product, Rational.one(),
    Rational.eq_one_of_positive_gap(n, p, d, k, proof),
    Equal.sym(Rational, product, simplified, Rational.mul_pure_negative_shape(p, n, d, k)),
    {==})

def Rational.inverse_cancel_by_difference(+p: Nat, +n: Nat, +d: Nat, difference: Z.Integer,
  specification: Z.Integer.SubtractSpec(p, n, difference),
  nonzero: Rational.Eq(Fraction{p, n, d}, Rational.zero()) -> Empty) ->
  Rational.Eq(Rational.mul(Fraction{p, n, d}, Rational.inverse_from_difference(d, difference)), Rational.one()):
  match difference:
    case Z.ZPos{magnitude}:
      match magnitude:
        case 0n:
          Empty.absurd(Rational.Eq(Rational.mul(Fraction{p, n, d}, Rational.zero()), Rational.one()),
            nonzero(Rational.eq_zero_if_balanced(p, n, d,
              Equal.trans(Nat,
                p, Nat.add(n, 0n), n,
                specification, N.Natural.add_zero(n)))))
        case 1n+k:
          Rational.inverse_positive_cancel(p, n, d, k, specification)
    case Z.ZNeg{predecessor}:
      Rational.inverse_negative_cancel(p, n, d, predecessor, specification)

def Rational.inverse_cancel(x: Rational, nonzero: Rational.Eq(x, Rational.zero()) -> Empty) -> Rational.Eq(Rational.mul(x, Rational.inverse(x)), Rational.one()):
  match x:
    case Fraction{+p, +n, +d}:
      Rational.inverse_cancel_by_difference(p, n, d,
        Z.Integer.subtract_naturals(p, n),
        Z.Integer.subtract_spec(p, n), nonzero)

def Rational.inverse_unique(+x: Rational, +u: Rational, +v: Rational,
  xu: Rational.Eq(Rational.mul(x, u), Rational.one()),
  xv: Rational.Eq(Rational.mul(x, v), Rational.one())) -> Rational.Eq(u, v):
  +u_one: Rational = Rational.mul(u, Rational.one())
  +u_xv: Rational = Rational.mul(u, Rational.mul(x, v))
  +xu_v: Rational = Rational.mul(Rational.mul(x, u), v)
  +one_v: Rational = Rational.mul(Rational.one(), v)
  Rational.eq_transitive(u, u_one, v,
    Rational.eq_from_structural(u, u_one,
      Equal.sym(Rational, u_one, u, Rational.mul_one(u))),
    Rational.eq_transitive(u_one, u_xv, v,
      Rational.eq_mul_left(Rational.one(), Rational.mul(x, v), u,
        Rational.eq_symmetric(Rational.mul(x, v), Rational.one(), xv)),
      Rational.eq_transitive(u_xv, xu_v, v,
        Rational.eq_from_structural(u_xv, xu_v,
          Rational.mul_swap_associative(u, x, v)),
        Rational.eq_transitive(xu_v, one_v, v,
          Rational.eq_mul_right(Rational.mul(x, u), Rational.one(), v, xu),
          Rational.eq_from_structural(one_v, v, Rational.one_mul(v))))))

def Rational.nonzero_transfer(+x: Rational, +y: Rational,
  equality: Rational.Eq(x, y),
  nonzero: Rational.Eq(x, Rational.zero()) -> Empty) ->
  Rational.Eq(y, Rational.zero()) -> Empty:
  contradiction => nonzero(Rational.eq_transitive(x, y, Rational.zero(), equality, contradiction))

def Rational.inverse_respects_nonzero_eq(+x: Rational, +y: Rational,
  equality: Rational.Eq(x, y),
  x_nonzero: Rational.Eq(x, Rational.zero()) -> Empty,
  y_nonzero: Rational.Eq(y, Rational.zero()) -> Empty) ->
  Rational.Eq(Rational.inverse(x), Rational.inverse(y)):
  +u: Rational = Rational.inverse(x)
  +v: Rational = Rational.inverse(y)
  +yu: Rational = Rational.mul(y, u)
  +xu: Rational = Rational.mul(x, u)
  Rational.inverse_unique(y, u, v,
    Rational.eq_transitive(yu, xu, Rational.one(),
      Rational.eq_symmetric(xu, yu, Rational.eq_mul_right(x, y, u, equality)),
      Rational.inverse_cancel(x, x_nonzero)),
    Rational.inverse_cancel(y, y_nonzero))

def Rational.inverse_respects_eq_by_cases(+x: Rational, +y: Rational,
  equality: Rational.Eq(x, y),
  x_case: Or(Rational.Eq(x, Rational.zero()), Rational.Eq(x, Rational.zero()) -> Empty),
  y_case: Or(Rational.Eq(y, Rational.zero()), Rational.Eq(y, Rational.zero()) -> Empty)) ->
  Rational.Eq(Rational.inverse(x), Rational.inverse(y)):
  match x_case y_case:
    case Inl{x_zero} Inl{y_zero}:
      Rational.eq_transitive(Rational.inverse(x), Rational.zero(), Rational.inverse(y),
        Rational.inverse_zero_if_eq(x, x_zero),
        Rational.eq_symmetric(Rational.inverse(y), Rational.zero(),
          Rational.inverse_zero_if_eq(y, y_zero)))
    case Inl{x_zero} Inr{y_nonzero}:
      Empty.absurd(Rational.Eq(Rational.inverse(x), Rational.inverse(y)),
        y_nonzero(Rational.eq_transitive(y, x, Rational.zero(),
          Rational.eq_symmetric(x, y, equality), x_zero)))
    case Inr{x_nonzero} Inl{y_zero}:
      Empty.absurd(Rational.Eq(Rational.inverse(x), Rational.inverse(y)),
        x_nonzero(Rational.eq_transitive(x, y, Rational.zero(), equality, y_zero)))
    case Inr{x_nonzero} Inr{y_nonzero}:
      Rational.inverse_respects_nonzero_eq(x, y, equality, x_nonzero, y_nonzero)

def Rational.inverse_respects_eq(+x: Rational, +y: Rational, equality: Rational.Eq(x, y)) -> Rational.Eq(Rational.inverse(x), Rational.inverse(y)):
  Rational.inverse_respects_eq_by_cases(x, y, equality,
    Rational.zero_or_nonzero(x), Rational.zero_or_nonzero(y))

def Rational.mul_add_distributive(+a: Rational, +b: Rational, +c: Rational) ->
  Rational.Eq(Rational.mul(a, Rational.add(b, c)), Rational.add(Rational.mul(a, b), Rational.mul(a, c))):
  +left: Rational = Rational.mul(a, Rational.add(b, c))
  +right: Rational = Rational.add(Rational.mul(a, b), Rational.mul(a, c))
  +scaled: Rational = Rational.scale(left, Rational.denominator_predecessor(a))
  Rational.eq_transitive(left, scaled, right,
    Rational.scale_preserves_eq(left, Rational.denominator_predecessor(a)),
    Rational.eq_from_structural(scaled, right,
      Rational.distributive_scaled_structural(a, b, c)))

def Rational.add_mul_distributive(+a: Rational, +b: Rational, +c: Rational) ->
  Rational.Eq(Rational.mul(Rational.add(a, b), c), Rational.add(Rational.mul(a, c), Rational.mul(b, c))):
  Rational.eq_structural_congruent(
    Rational.mul(c, Rational.add(a, b)),
    Rational.add(Rational.mul(c, a), Rational.mul(c, b)),
    Rational.mul(Rational.add(a, b), c),
    Rational.add(Rational.mul(a, c), Rational.mul(b, c)),
    Rational.mul_add_distributive(c, a, b),
    Rational.mul_commutative(c, Rational.add(a, b)),
    Rational.add_structural_congruent(
      Rational.mul(c, a), Rational.mul(c, b), Rational.mul(a, c), Rational.mul(b, c),
      Rational.mul_commutative(c, a), Rational.mul_commutative(c, b)))

def Rational.two_power_predecessor(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+Nat.double(Rational.two_power_predecessor(p))

def Rational.dyadic(n: Nat) -> Rational:
  Fraction{1n, 0n, Rational.two_power_predecessor(n)}

def Rational.dyadic_denominator_next(n: Nat) ->
  {Rational.denominator(Rational.dyadic(1n+n)) ==
   Nat.add(Rational.denominator(Rational.dyadic(n)), Rational.denominator(Rational.dyadic(n))) : Nat}:
  N.Natural.successor_double(Rational.two_power_predecessor(n))

def Rational.two_unit_halves(+half_predecessor: Nat, +whole_predecessor: Nat,
  equality: {1n+half_predecessor == Nat.add(1n+whole_predecessor, 1n+whole_predecessor) : Nat}) ->
  Rational.Eq(
    Rational.add(Fraction{1n, 0n, half_predecessor}, Fraction{1n, 0n, half_predecessor}),
    Fraction{1n, 0n, whole_predecessor}):
  +half_denominator: Nat = 1n+half_predecessor
  +whole_denominator: Nat = 1n+whole_predecessor
  +sum_denominator: Nat = 1n+Rational.denominator_product(half_predecessor, half_predecessor)
  +positive_sum: Nat = Nat.add(Nat.mul(1n, half_denominator), Nat.mul(1n, half_denominator))
  Equal.cong(Nat, Nat, z => Nat.add(z, 0n),
    Nat.mul(positive_sum, whole_denominator),
    Nat.mul(1n, sum_denominator),
    Equal.trans(Nat,
      Nat.mul(positive_sum, whole_denominator),
      Nat.mul(1n, Nat.mul(half_denominator, half_denominator)),
      Nat.mul(1n, sum_denominator),
      N.Natural.two_unit_cross(half_denominator, whole_denominator, equality),
      Equal.cong(Nat, Nat, z => Nat.mul(1n, z),
        Nat.mul(half_denominator, half_denominator), sum_denominator,
        Equal.sym(Nat,
          sum_denominator, Nat.mul(half_denominator, half_denominator),
          Rational.denominator_product_spec(half_predecessor, half_predecessor)))))

def Rational.dyadic_double(+n: Nat) ->
  Rational.Eq(
    Rational.add(Rational.dyadic(1n+n), Rational.dyadic(1n+n)),
    Rational.dyadic(n)):
  Rational.two_unit_halves(
    Rational.two_power_predecessor(1n+n),
    Rational.two_power_predecessor(n),
    Rational.dyadic_denominator_next(n))

def Rational.close_halve_errors(+x: Rational, +y: Rational, +n: Nat, +m: Nat,
  proof: Rational.Close(x, y,
    Rational.add(Rational.dyadic(1n+n), Rational.dyadic(1n+n)),
    Rational.add(Rational.dyadic(1n+m), Rational.dyadic(1n+m)))) ->
  Rational.Close(x, y, Rational.dyadic(n), Rational.dyadic(m)):
  Rational.close_replace_errors(x, y,
    Rational.add(Rational.dyadic(1n+n), Rational.dyadic(1n+n)),
    Rational.add(Rational.dyadic(1n+m), Rational.dyadic(1n+m)),
    Rational.dyadic(n), Rational.dyadic(m), proof,
    Rational.eq_add_both(
      Rational.add(Rational.dyadic(1n+n), Rational.dyadic(1n+n)), Rational.dyadic(n),
      Rational.add(Rational.dyadic(1n+m), Rational.dyadic(1n+m)), Rational.dyadic(m),
      Rational.dyadic_double(n), Rational.dyadic_double(m)),
    Rational.eq_add_both(
      Rational.add(Rational.dyadic(1n+m), Rational.dyadic(1n+m)), Rational.dyadic(m),
      Rational.add(Rational.dyadic(1n+n), Rational.dyadic(1n+n)), Rational.dyadic(n),
      Rational.dyadic_double(m), Rational.dyadic_double(n)))

def Rational.dyadic_nonnegative(n: Nat) -> Rational.Le(Rational.zero(), Rational.dyadic(n)):
  N.Natural.zero_le(1n)
