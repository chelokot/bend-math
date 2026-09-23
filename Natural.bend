import Base

def Natural.Le(a: Nat, b: Nat) -> Type:
  match a b:
    case 0n 0n:
      Unit
    case 0n 1n+bp:
      Unit
    case 1n+ap 0n:
      Empty
    case 1n+ap 1n+bp:
      Natural.Le(ap, bp)

def Natural.le_reflexive(n: Nat) -> Natural.Le(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      Natural.le_reflexive(p)

def Natural.zero_le(n: Nat) -> Natural.Le(0n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      Unit{}

def Natural.le_add_right(a: Nat, +b: Nat) -> Natural.Le(a, Nat.add(a, b)):
  match a:
    case 0n:
      Natural.zero_le(b)
    case 1n+p:
      Natural.le_add_right(p, b)

def Natural.le_add_both_left(c: Nat, a: Nat, b: Nat, proof: Natural.Le(a, b)) -> Natural.Le(Nat.add(c, a), Nat.add(c, b)):
  match c:
    case 0n:
      proof
    case 1n+p:
      Natural.le_add_both_left(p, a, b, proof)

def Natural.le_transitive(a: Nat, b: Nat, c: Nat, ab: Natural.Le(a, b), bc: Natural.Le(b, c)) -> Natural.Le(a, c):
  match a:
    case 0n:
      match c:
        case 0n:
          Unit{}
        case 1n+cp:
          Unit{}
    case 1n+ap:
      match b:
        case 0n:
          match ab:
        case 1n+bp:
          match c:
            case 0n:
              match bc:
            case 1n+cp:
              Natural.le_transitive(ap, bp, cp, ab, bc)

def Natural.le_antisymmetric(a: Nat, b: Nat, ab: Natural.Le(a, b), ba: Natural.Le(b, a)) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      match ba:
    case 1n+ap 0n:
      match ab:
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, z => 1n+z, ap, bp, Natural.le_antisymmetric(ap, bp, ab, ba))

def Natural.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, Natural.add_zero(p))

def Natural.add_successor(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), Natural.add_successor(p, b))

def Natural.add_commutative(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Natural.add_zero(b))
    case 1n++p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), Natural.add_commutative(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Natural.add_successor(b, p)))

def Natural.add_associative(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), Natural.add_associative(p, b, c))

def Natural.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat,
    Nat.add(a, Nat.add(b, c)),
    Nat.add(Nat.add(a, b), c),
    Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Natural.add_associative(a, b, c)),
    Equal.trans(Nat,
      Nat.add(Nat.add(a, b), c),
      Nat.add(Nat.add(b, a), c),
      Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, z => Nat.add(z, c), Nat.add(a, b), Nat.add(b, a), Natural.add_commutative(a, b)),
      Natural.add_associative(b, a, c)))

def Natural.eq_add_swap(+a: Nat, +b: Nat, +c: Nat, +d: Nat, proof: {Nat.add(b, a) == Nat.add(d, c) : Nat}) -> {Nat.add(a, b) == Nat.add(c, d) : Nat}:
  Equal.trans(Nat,
    Nat.add(a, b),
    Nat.add(b, a),
    Nat.add(c, d),
    Natural.add_commutative(a, b),
    Equal.trans(Nat,
      Nat.add(b, a),
      Nat.add(d, c),
      Nat.add(c, d),
      proof,
      Natural.add_commutative(d, c)))

def Natural.le_congruent(+a: Nat, +b: Nat, +c: Nat, +d: Nat, proof: Natural.Le(a, b), ac: {a == c : Nat}, bd: {b == d : Nat}) -> Natural.Le(c, d):
  %ac : Natural.Le(_, d)
  %bd : Natural.Le(a, _)
  proof

def Natural.mul_zero(n: Nat) -> {Nat.mul(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Natural.mul_zero(p)

def Natural.mul_one(n: Nat) -> {Nat.mul(n, 1n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.mul(p, 1n), p, Natural.mul_one(p))

def Natural.one_mul(n: Nat) -> {Nat.mul(1n, n) == n : Nat}:
  Natural.add_zero(n)

def Natural.mul_add_left(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(c, Nat.mul(Nat.add(p, b), c)),
        Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
        Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
        Equal.cong(Nat, Nat, z => Nat.add(c, z), Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), Natural.mul_add_left(p, b, c)),
        Equal.sym(Nat,
          Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
          Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
          Natural.add_associative(c, Nat.mul(p, c), Nat.mul(b, c))))

def Natural.mul_successor_right(a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(1n+b, Nat.mul(p, 1n+b)),
        Nat.add(1n+b, Nat.add(p, Nat.mul(p, b))),
        Nat.add(1n+p, Nat.add(b, Nat.mul(p, b))),
        Equal.cong(Nat, Nat, z => Nat.add(1n+b, z), Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), Natural.mul_successor_right(p, b)),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(p, Nat.add(b, Nat.mul(p, b))), Natural.add_swap(b, p, Nat.mul(p, b))))

def Natural.mul_commutative(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, Natural.mul_zero(b))
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(b, Nat.mul(p, b)),
        Nat.add(b, Nat.mul(b, p)),
        Nat.mul(b, 1n+p),
        Equal.cong(Nat, Nat, z => Nat.add(b, z), Nat.mul(p, b), Nat.mul(b, p), Natural.mul_commutative(p, b)),
        Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), Natural.mul_successor_right(b, p)))

def Natural.mul_associative(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.mul(Nat.add(b, Nat.mul(p, b)), c),
        Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)),
        Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))),
        Natural.mul_add_left(b, Nat.mul(p, b), c),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(b, c), z), Nat.mul(Nat.mul(p, b), c), Nat.mul(p, Nat.mul(b, c)), Natural.mul_associative(p, b, c)))

def Natural.mul_add_right(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(a, Nat.add(b, c)),
    Nat.mul(Nat.add(b, c), a),
    Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
    Natural.mul_commutative(a, Nat.add(b, c)),
    Equal.trans(Nat,
      Nat.mul(Nat.add(b, c), a),
      Nat.add(Nat.mul(b, a), Nat.mul(c, a)),
      Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
      Natural.mul_add_left(b, c, a),
      Equal.trans(Nat,
        Nat.add(Nat.mul(b, a), Nat.mul(c, a)),
        Nat.add(Nat.mul(a, b), Nat.mul(c, a)),
        Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(c, a)), Nat.mul(b, a), Nat.mul(a, b), Natural.mul_commutative(b, a)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(a, b), z), Nat.mul(c, a), Nat.mul(a, c), Natural.mul_commutative(c, a)))))
