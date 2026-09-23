import Base
import ./Natural.bend as N

type Integer is Data:
  ZPos{magnitude: Nat}
  ZNeg{predecessor: Nat}

def Integer.zero() -> Integer:
  ZPos{0n}

def Integer.one() -> Integer:
  ZPos{1n}

def Integer.of_nat(n: Nat) -> Integer:
  ZPos{n}

def Integer.neg(x: Integer) -> Integer:
  match x:
    case ZPos{magnitude}:
      match magnitude:
        case 0n:
          ZPos{0n}
        case 1n+p:
          ZNeg{p}
    case ZNeg{predecessor}:
      ZPos{1n+predecessor}

def Integer.subtract_naturals(a: Nat, b: Nat) -> Integer:
  match a b:
    case 0n 0n:
      ZPos{0n}
    case 0n 1n+bp:
      ZNeg{bp}
    case 1n+ap 0n:
      ZPos{1n+ap}
    case 1n+ap 1n+bp:
      Integer.subtract_naturals(ap, bp)

def Integer.subtract_same(n: Nat) -> {Integer.subtract_naturals(n, n) == Integer.zero() : Integer}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Integer.subtract_same(p)

def Integer.add(a: Integer, b: Integer) -> Integer:
  match a b:
    case ZPos{x} ZPos{y}:
      ZPos{Nat.add(x, y)}
    case ZPos{x} ZNeg{y}:
      Integer.subtract_naturals(x, 1n+y)
    case ZNeg{x} ZPos{y}:
      Integer.subtract_naturals(y, 1n+x)
    case ZNeg{x} ZNeg{y}:
      ZNeg{1n+Nat.add(x, y)}

def Integer.mul(a: Integer, b: Integer) -> Integer:
  match a b:
    case ZPos{x} ZPos{y}:
      ZPos{Nat.mul(x, y)}
    case ZPos{x} ZNeg{y}:
      Integer.neg(ZPos{Nat.mul(x, 1n+y)})
    case ZNeg{x} ZPos{y}:
      Integer.neg(ZPos{Nat.mul(1n+x, y)})
    case ZNeg{x} ZNeg{y}:
      ZPos{Nat.mul(1n+x, 1n+y)}

def Integer.abs(x: Integer) -> Integer:
  match x:
    case ZPos{magnitude}:
      ZPos{magnitude}
    case ZNeg{predecessor}:
      ZPos{1n+predecessor}

def Integer.Le(a: Integer, b: Integer) -> Type:
  match a b:
    case ZPos{x} ZPos{y}:
      N.Natural.Le(x, y)
    case ZPos{x} ZNeg{y}:
      Empty
    case ZNeg{x} ZPos{y}:
      Unit
    case ZNeg{x} ZNeg{y}:
      N.Natural.Le(y, x)

def Integer.le_reflexive(x: Integer) -> Integer.Le(x, x):
  match x:
    case ZPos{magnitude}:
      N.Natural.le_reflexive(magnitude)
    case ZNeg{predecessor}:
      N.Natural.le_reflexive(predecessor)

def Integer.neg_involutive(x: Integer) -> {Integer.neg(Integer.neg(x)) == x : Integer}:
  match x:
    case ZPos{magnitude}:
      match magnitude:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case ZNeg{predecessor}:
      {==}

def Integer.zero_add(x: Integer) -> {Integer.add(Integer.zero(), x) == x : Integer}:
  match x:
    case ZPos{magnitude}:
      {==}
    case ZNeg{predecessor}:
      {==}

def Integer.add_zero(x: Integer) -> {Integer.add(x, Integer.zero()) == x : Integer}:
  match x:
    case ZPos{magnitude}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.add(magnitude, 0n), magnitude, N.Natural.add_zero(magnitude))
    case ZNeg{predecessor}:
      {==}

def Integer.add_commutative(a: Integer, b: Integer) -> {Integer.add(a, b) == Integer.add(b, a) : Integer}:
  match a b:
    case ZPos{x} ZPos{y}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.add(x, y), Nat.add(y, x), N.Natural.add_commutative(x, y))
    case ZPos{x} ZNeg{y}:
      {==}
    case ZNeg{x} ZPos{y}:
      {==}
    case ZNeg{x} ZNeg{y}:
      Equal.cong(Nat, Integer, z => ZNeg{1n+z}, Nat.add(x, y), Nat.add(y, x), N.Natural.add_commutative(x, y))

def Integer.mul_commutative(a: Integer, b: Integer) -> {Integer.mul(a, b) == Integer.mul(b, a) : Integer}:
  match a b:
    case ZPos{x} ZPos{y}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.mul(x, y), Nat.mul(y, x), N.Natural.mul_commutative(x, y))
    case ZPos{x} ZNeg{y}:
      Equal.cong(Nat, Integer, z => Integer.neg(ZPos{z}), Nat.mul(x, 1n+y), Nat.mul(1n+y, x), N.Natural.mul_commutative(x, 1n+y))
    case ZNeg{x} ZPos{y}:
      Equal.cong(Nat, Integer, z => Integer.neg(ZPos{z}), Nat.mul(1n+x, y), Nat.mul(y, 1n+x), N.Natural.mul_commutative(1n+x, y))
    case ZNeg{x} ZNeg{y}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.mul(1n+x, 1n+y), Nat.mul(1n+y, 1n+x), N.Natural.mul_commutative(1n+x, 1n+y))

def Integer.mul_zero(x: Integer) -> {Integer.mul(x, Integer.zero()) == Integer.zero() : Integer}:
  match x:
    case ZPos{magnitude}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.mul(magnitude, 0n), 0n, N.Natural.mul_zero(magnitude))
    case ZNeg{predecessor}:
      Equal.cong(Nat, Integer, z => Integer.neg(ZPos{z}), Nat.mul(1n+predecessor, 0n), 0n, N.Natural.mul_zero(1n+predecessor))

def Integer.zero_mul(x: Integer) -> {Integer.mul(Integer.zero(), x) == Integer.zero() : Integer}:
  match x:
    case ZPos{magnitude}:
      {==}
    case ZNeg{predecessor}:
      {==}

def Integer.mul_one(x: Integer) -> {Integer.mul(x, Integer.one()) == x : Integer}:
  match x:
    case ZPos{magnitude}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.mul(magnitude, 1n), magnitude, N.Natural.mul_one(magnitude))
    case ZNeg{predecessor}:
      Equal.cong(Nat, Integer, z => Integer.neg(ZPos{z}), Nat.mul(1n+predecessor, 1n), 1n+predecessor, N.Natural.mul_one(1n+predecessor))

def Integer.one_mul(x: Integer) -> {Integer.mul(Integer.one(), x) == x : Integer}:
  match x:
    case ZPos{magnitude}:
      Equal.cong(Nat, Integer, z => ZPos{z}, Nat.mul(1n, magnitude), magnitude, N.Natural.one_mul(magnitude))
    case ZNeg{predecessor}:
      Equal.cong(Nat, Integer, z => Integer.neg(ZPos{z}), Nat.mul(1n, 1n+predecessor), 1n+predecessor, N.Natural.one_mul(1n+predecessor))

def Integer.add_neg_self(x: Integer) -> {Integer.add(x, Integer.neg(x)) == Integer.zero() : Integer}:
  match x:
    case ZPos{magnitude}:
      match magnitude:
        case 0n:
          {==}
        case 1n+p:
          Integer.subtract_same(1n+p)
    case ZNeg{predecessor}:
      Integer.subtract_same(1n+predecessor)
