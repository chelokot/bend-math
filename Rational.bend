import Base
import ./Natural.bend as N
import ./Integer.bend as Z

type Rational is Data:
  Fraction{positive: Nat, negative: Nat, denominator_predecessor: Nat}

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

def Rational.add(a: Rational, b: Rational) -> Rational:
  match a b:
    case Fraction{+ap, +an, +ad} Fraction{+bp, +bn, +bd}:
      Fraction{
        Nat.add(Nat.mul(ap, 1n+bd), Nat.mul(bp, 1n+ad)),
        Nat.add(Nat.mul(an, 1n+bd), Nat.mul(bn, 1n+ad)),
        Rational.denominator_product(ad, bd)
      }

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

def Rational.left_cross(+x: Rational, +y: Rational) -> Nat:
  Nat.add(Nat.mul(Rational.positive(x), Rational.denominator(y)), Nat.mul(Rational.negative(y), Rational.denominator(x)))

def Rational.right_cross(+x: Rational, +y: Rational) -> Nat:
  Nat.add(Nat.mul(Rational.positive(y), Rational.denominator(x)), Nat.mul(Rational.negative(x), Rational.denominator(y)))

def Rational.Eq(+x: Rational, +y: Rational) -> Type:
  {Rational.left_cross(x, y) == Rational.right_cross(x, y) : Nat}

def Rational.Le(+x: Rational, +y: Rational) -> Type:
  N.Natural.Le(Rational.left_cross(x, y), Rational.right_cross(x, y))

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

def Rational.two_power_predecessor(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      1n+Nat.double(Rational.two_power_predecessor(p))

def Rational.dyadic(n: Nat) -> Rational:
  Fraction{1n, 0n, Rational.two_power_predecessor(n)}
