import Base
import ./Natural.bend as N

def Bits.Holds(b: Bool) -> Kind(&2):
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def Bits.n(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def Bits.count(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(Bits.n(x), Bits.count(rest))

def Bits.length(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      1n+Bits.length(rest)

def Bits.get(xs: List<&2, Bool>, index: Nat) -> Bool:
  match xs index:
    case Nil{} _:
      False{}
    case x <> rest 0n:
      x
    case x <> rest 1n+previous:
      Bits.get(rest, previous)

def Bits.union(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      ys
    case x <> xs_rest:
      match ys:
        case Nil{}:
          Con{x, xs_rest}
        case y <> ys_rest:
          Con{Bool.or(x, y), Bits.union(xs_rest, ys_rest)}

def Bits.mask(+keep: Bool, xs: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Con{Bool.and(keep, x), Bits.mask(keep, rest)}

def Bits.meet(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> xs_rest:
      match ys:
        case Nil{}:
          False{}
        case y <> ys_rest:
          Bool.or(Bool.and(x, y), Bits.meet(xs_rest, ys_rest))

type Bits.Pairs is Data:
  NoPairs{}
  MorePairs{first: Nat, second: Nat, rest: Bits.Pairs}

def Bits.touches(pairs: Bits.Pairs, +xs: List<&2, Bool>, +ys: List<&2, Bool>) -> Bool:
  match pairs:
    case NoPairs{}:
      False{}
    case MorePairs{first, second, rest}:
      Bool.or(Bool.and(Bits.get(xs, first), Bits.get(ys, second)), Bits.touches(rest, xs, ys))

def Bits.split(b: Bool) -> Or(Bits.Holds(b), Bits.Holds(Bool.not(b))):
  match b:
    case False{}:
      Inr{Unit{}}
    case True{}:
      Inl{Unit{}}

def Bits.both(a: Bool, +b: Bool, first: Bits.Holds(a), second: Bits.Holds(b)) -> Bits.Holds(Bool.and(a, b)):
  match a:
    case False{}:
      match first:
    case True{}:
      second

def Bits.left(a: Bool, +b: Bool, both: Bits.Holds(Bool.and(a, b))) -> Bits.Holds(a):
  match a:
    case False{}:
      match both:
    case True{}:
      Unit{}

def Bits.right(a: Bool, +b: Bool, both: Bits.Holds(Bool.and(a, b))) -> Bits.Holds(b):
  match a:
    case False{}:
      match both:
    case True{}:
      both

def Bits.either(a: Bool, +b: Bool, any: Bits.Holds(Bool.or(a, b))) -> Or(Bits.Holds(a), Bits.Holds(b)):
  match a:
    case False{}:
      Inr{any}
    case True{}:
      Inl{Unit{}}

def Bits.neither_left(a: Bool, +b: Bool, none: Bits.Holds(Bool.not(Bool.or(a, b)))) -> Bits.Holds(Bool.not(a)):
  match a:
    case False{}:
      Unit{}
    case True{}:
      match none:

def Bits.neither_right(a: Bool, +b: Bool, none: Bits.Holds(Bool.not(Bool.or(a, b)))) -> Bits.Holds(Bool.not(b)):
  match a:
    case False{}:
      none
    case True{}:
      match none:

def Bits.neither(a: Bool, +b: Bool, first: Bits.Holds(Bool.not(a)), second: Bits.Holds(Bool.not(b))) -> Bits.Holds(Bool.not(Bool.or(a, b))):
  match a:
    case False{}:
      second
    case True{}:
      match first:

def Bits.never(a: Bool, yes: Bits.Holds(a), no: Bits.Holds(Bool.not(a))) -> Empty:
  match a:
    case False{}:
      match yes:
    case True{}:
      match no:

def Bits.transport(+a: Bool, +b: Bool, same: {a == b : Bool}, holds: Bits.Holds(a)) -> Bits.Holds(b):
  %same : Bits.Holds(_)
  holds

def Bits.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Bits.distributes(x: Bool, +y: Bool, +z: Bool, +a: Bool, +b: Bool) ->
  {Bool.or(Bool.and(Bool.or(x, y), z), Bool.or(a, b)) == Bool.or(Bool.or(Bool.and(x, z), a), Bool.or(Bool.and(y, z), b)) : Bool}:
  match x y z a b:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

def Bits.count_union_step(x: Bool, y: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>,
  disjoint: Bits.Holds(Bool.not(Bool.or(Bool.and(x, y), Bits.meet(xs, ys)))),
  rest: Bits.Holds(Bool.not(Bits.meet(xs, ys))) -> {Bits.count(Bits.union(xs, ys)) == Nat.add(Bits.count(xs), Bits.count(ys)) : Nat}) ->
  {Bits.count(Bits.union(Con{x, xs}, Con{y, ys})) == Nat.add(Bits.count(Con{x, xs}), Bits.count(Con{y, ys})) : Nat}:
  match x y:
    case False{} False{}:
      rest(disjoint)
    case False{} True{}:
      Equal.trans(Nat,
        1n+Bits.count(Bits.union(xs, ys)),
        1n+Nat.add(Bits.count(xs), Bits.count(ys)),
        Nat.add(Bits.count(xs), 1n+Bits.count(ys)),
        Equal.cong(Nat, Nat, z => 1n+z, Bits.count(Bits.union(xs, ys)), Nat.add(Bits.count(xs), Bits.count(ys)), rest(disjoint)),
        Equal.sym(Nat, Nat.add(Bits.count(xs), 1n+Bits.count(ys)), 1n+Nat.add(Bits.count(xs), Bits.count(ys)),
          N.Natural.add_successor(Bits.count(xs), Bits.count(ys))))
    case True{} False{}:
      Equal.cong(Nat, Nat, z => 1n+z, Bits.count(Bits.union(xs, ys)), Nat.add(Bits.count(xs), Bits.count(ys)), rest(disjoint))
    case True{} True{}:
      match disjoint:

def Bits.count_union(+xs: List<&2, Bool>, +ys: List<&2, Bool>, disjoint: Bits.Holds(Bool.not(Bits.meet(xs, ys)))) ->
  {Bits.count(Bits.union(xs, ys)) == Nat.add(Bits.count(xs), Bits.count(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> xs_rest:
      match ys:
        case Nil{}:
          Equal.sym(Nat, Nat.add(Bits.count(Con{x, xs_rest}), 0n), Bits.count(Con{x, xs_rest}), N.Natural.add_zero(Bits.count(Con{x, xs_rest})))
        case y <> ys_rest:
          Bits.count_union_step(x, y, xs_rest, ys_rest, disjoint, rest => Bits.count_union(xs_rest, ys_rest, rest))

def Bits.le_successor(n: Nat) -> N.Natural.Le(n, 1n+n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      Bits.le_successor(p)

def Bits.count_at_most_length(+xs: List<&2, Bool>) -> N.Natural.Le(Bits.count(xs), Bits.length(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case x <> rest:
      match x:
        case False{}:
          N.Natural.le_transitive(Bits.count(rest), Bits.length(rest), 1n+Bits.length(rest),
            Bits.count_at_most_length(rest), Bits.le_successor(Bits.length(rest)))
        case True{}:
          Bits.count_at_most_length(rest)

def Bits.meet_union(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>) ->
  {Bits.meet(Bits.union(xs, ys), zs) == Bool.or(Bits.meet(xs, zs), Bits.meet(ys, zs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> xs_rest:
      match ys:
        case Nil{}:
          Equal.sym(Bool, Bool.or(Bits.meet(Con{x, xs_rest}, zs), False{}), Bits.meet(Con{x, xs_rest}, zs), Bits.or_false(Bits.meet(Con{x, xs_rest}, zs)))
        case y <> ys_rest:
          match zs:
            case Nil{}:
              {==}
            case z <> zs_rest:
              Equal.trans(Bool,
                Bool.or(Bool.and(Bool.or(x, y), z), Bits.meet(Bits.union(xs_rest, ys_rest), zs_rest)),
                Bool.or(Bool.and(Bool.or(x, y), z), Bool.or(Bits.meet(xs_rest, zs_rest), Bits.meet(ys_rest, zs_rest))),
                Bool.or(Bool.or(Bool.and(x, z), Bits.meet(xs_rest, zs_rest)), Bool.or(Bool.and(y, z), Bits.meet(ys_rest, zs_rest))),
                Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bool.or(x, y), z), w),
                  Bits.meet(Bits.union(xs_rest, ys_rest), zs_rest), Bool.or(Bits.meet(xs_rest, zs_rest), Bits.meet(ys_rest, zs_rest)),
                  Bits.meet_union(xs_rest, ys_rest, zs_rest)),
                Bits.distributes(x, y, z, Bits.meet(xs_rest, zs_rest), Bits.meet(ys_rest, zs_rest)))

def Bits.and_false(a: Bool, +b: Bool) -> {Bool.and(a, Bool.and(b, False{})) == False{} : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}
def Bits.distributes_right(x: Bool, +y: Bool, +z: Bool, +a: Bool, +b: Bool) ->
  {Bool.or(Bool.and(x, Bool.or(y, z)), Bool.or(a, b)) == Bool.or(Bool.or(Bool.and(x, y), a), Bool.or(Bool.and(x, z), b)) : Bool}:
  match x y z a b:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

def Bits.masked(a: Bool, +b: Bool, +x: Bool, +y: Bool, +t: Bool) ->
  {Bool.or(Bool.and(Bool.and(a, x), Bool.and(b, y)), Bool.and(a, Bool.and(b, t))) == Bool.and(a, Bool.and(b, Bool.or(Bool.and(x, y), t))) : Bool}:
  match a b x y t:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

def Bits.get_union(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +index: Nat) ->
  {Bits.get(Bits.union(xs, ys), index) == Bool.or(Bits.get(xs, index), Bits.get(ys, index)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> xs_rest:
      match ys:
        case Nil{}:
          Equal.sym(Bool, Bool.or(Bits.get(Con{x, xs_rest}, index), False{}), Bits.get(Con{x, xs_rest}, index),
            Bits.or_false(Bits.get(Con{x, xs_rest}, index)))
        case y <> ys_rest:
          match index:
            case 0n:
              {==}
            case 1n+previous:
              Bits.get_union(xs_rest, ys_rest, previous)

def Bits.and_false_right(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Bits.get_mask(+keep: Bool, +xs: List<&2, Bool>, +index: Nat) ->
  {Bits.get(Bits.mask(keep, xs), index) == Bool.and(keep, Bits.get(xs, index)) : Bool}:
  match xs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(keep, False{}), False{}, Bits.and_false_right(keep))
    case x <> rest:
      match index:
        case 0n:
          {==}
        case 1n+previous:
          Bits.get_mask(keep, rest, previous)

def Bits.touches_union_left(pairs: Bits.Pairs, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>) ->
  {Bits.touches(pairs, Bits.union(xs, ys), zs) == Bool.or(Bits.touches(pairs, xs, zs), Bits.touches(pairs, ys, zs)) : Bool}:
  match pairs:
    case NoPairs{}:
      {==}
    case MorePairs{+first, +second, +rest}:
      Equal.trans(Bool,
        Bool.or(Bool.and(Bits.get(Bits.union(xs, ys), first), Bits.get(zs, second)), Bits.touches(rest, Bits.union(xs, ys), zs)),
        Bool.or(Bool.and(Bool.or(Bits.get(xs, first), Bits.get(ys, first)), Bits.get(zs, second)),
          Bool.or(Bits.touches(rest, xs, zs), Bits.touches(rest, ys, zs))),
        Bool.or(Bool.or(Bool.and(Bits.get(xs, first), Bits.get(zs, second)), Bits.touches(rest, xs, zs)),
          Bool.or(Bool.and(Bits.get(ys, first), Bits.get(zs, second)), Bits.touches(rest, ys, zs))),
        Equal.trans(Bool,
          Bool.or(Bool.and(Bits.get(Bits.union(xs, ys), first), Bits.get(zs, second)), Bits.touches(rest, Bits.union(xs, ys), zs)),
          Bool.or(Bool.and(Bool.or(Bits.get(xs, first), Bits.get(ys, first)), Bits.get(zs, second)), Bits.touches(rest, Bits.union(xs, ys), zs)),
          Bool.or(Bool.and(Bool.or(Bits.get(xs, first), Bits.get(ys, first)), Bits.get(zs, second)),
            Bool.or(Bits.touches(rest, xs, zs), Bits.touches(rest, ys, zs))),
          Equal.cong(Bool, Bool, w => Bool.or(Bool.and(w, Bits.get(zs, second)), Bits.touches(rest, Bits.union(xs, ys), zs)),
            Bits.get(Bits.union(xs, ys), first), Bool.or(Bits.get(xs, first), Bits.get(ys, first)), Bits.get_union(xs, ys, first)),
          Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bool.or(Bits.get(xs, first), Bits.get(ys, first)), Bits.get(zs, second)), w),
            Bits.touches(rest, Bits.union(xs, ys), zs), Bool.or(Bits.touches(rest, xs, zs), Bits.touches(rest, ys, zs)),
            Bits.touches_union_left(rest, xs, ys, zs))),
        Bits.distributes(Bits.get(xs, first), Bits.get(ys, first), Bits.get(zs, second), Bits.touches(rest, xs, zs), Bits.touches(rest, ys, zs)))

def Bits.touches_union_right(pairs: Bits.Pairs, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>) ->
  {Bits.touches(pairs, xs, Bits.union(ys, zs)) == Bool.or(Bits.touches(pairs, xs, ys), Bits.touches(pairs, xs, zs)) : Bool}:
  match pairs:
    case NoPairs{}:
      {==}
    case MorePairs{+first, +second, +rest}:
      Equal.trans(Bool,
        Bool.or(Bool.and(Bits.get(xs, first), Bits.get(Bits.union(ys, zs), second)), Bits.touches(rest, xs, Bits.union(ys, zs))),
        Bool.or(Bool.and(Bits.get(xs, first), Bool.or(Bits.get(ys, second), Bits.get(zs, second))),
          Bool.or(Bits.touches(rest, xs, ys), Bits.touches(rest, xs, zs))),
        Bool.or(Bool.or(Bool.and(Bits.get(xs, first), Bits.get(ys, second)), Bits.touches(rest, xs, ys)),
          Bool.or(Bool.and(Bits.get(xs, first), Bits.get(zs, second)), Bits.touches(rest, xs, zs))),
        Equal.trans(Bool,
          Bool.or(Bool.and(Bits.get(xs, first), Bits.get(Bits.union(ys, zs), second)), Bits.touches(rest, xs, Bits.union(ys, zs))),
          Bool.or(Bool.and(Bits.get(xs, first), Bool.or(Bits.get(ys, second), Bits.get(zs, second))), Bits.touches(rest, xs, Bits.union(ys, zs))),
          Bool.or(Bool.and(Bits.get(xs, first), Bool.or(Bits.get(ys, second), Bits.get(zs, second))),
            Bool.or(Bits.touches(rest, xs, ys), Bits.touches(rest, xs, zs))),
          Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bits.get(xs, first), w), Bits.touches(rest, xs, Bits.union(ys, zs))),
            Bits.get(Bits.union(ys, zs), second), Bool.or(Bits.get(ys, second), Bits.get(zs, second)), Bits.get_union(ys, zs, second)),
          Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bits.get(xs, first), Bool.or(Bits.get(ys, second), Bits.get(zs, second))), w),
            Bits.touches(rest, xs, Bits.union(ys, zs)), Bool.or(Bits.touches(rest, xs, ys), Bits.touches(rest, xs, zs)),
            Bits.touches_union_right(rest, xs, ys, zs))),
        Bits.distributes_right(Bits.get(xs, first), Bits.get(ys, second), Bits.get(zs, second), Bits.touches(rest, xs, ys), Bits.touches(rest, xs, zs)))

def Bits.touches_mask(pairs: Bits.Pairs, +a: Bool, +b: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>) ->
  {Bits.touches(pairs, Bits.mask(a, xs), Bits.mask(b, ys)) == Bool.and(a, Bool.and(b, Bits.touches(pairs, xs, ys))) : Bool}:
  match pairs:
    case NoPairs{}:
      Equal.sym(Bool, Bool.and(a, Bool.and(b, False{})), False{}, Bits.and_false(a, b))
    case MorePairs{+first, +second, +rest}:
      Equal.trans(Bool,
        Bool.or(Bool.and(Bits.get(Bits.mask(a, xs), first), Bits.get(Bits.mask(b, ys), second)), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
        Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bool.and(b, Bits.get(ys, second))), Bool.and(a, Bool.and(b, Bits.touches(rest, xs, ys)))),
        Bool.and(a, Bool.and(b, Bool.or(Bool.and(Bits.get(xs, first), Bits.get(ys, second)), Bits.touches(rest, xs, ys)))),
        Equal.trans(Bool,
          Bool.or(Bool.and(Bits.get(Bits.mask(a, xs), first), Bits.get(Bits.mask(b, ys), second)), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
          Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bits.get(Bits.mask(b, ys), second)), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
          Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bool.and(b, Bits.get(ys, second))), Bool.and(a, Bool.and(b, Bits.touches(rest, xs, ys)))),
          Equal.cong(Bool, Bool, w => Bool.or(Bool.and(w, Bits.get(Bits.mask(b, ys), second)), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
            Bits.get(Bits.mask(a, xs), first), Bool.and(a, Bits.get(xs, first)), Bits.get_mask(a, xs, first)),
          Equal.trans(Bool,
            Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bits.get(Bits.mask(b, ys), second)), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
            Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bool.and(b, Bits.get(ys, second))), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
            Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bool.and(b, Bits.get(ys, second))), Bool.and(a, Bool.and(b, Bits.touches(rest, xs, ys)))),
            Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), w), Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys))),
              Bits.get(Bits.mask(b, ys), second), Bool.and(b, Bits.get(ys, second)), Bits.get_mask(b, ys, second)),
            Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bool.and(a, Bits.get(xs, first)), Bool.and(b, Bits.get(ys, second))), w),
              Bits.touches(rest, Bits.mask(a, xs), Bits.mask(b, ys)), Bool.and(a, Bool.and(b, Bits.touches(rest, xs, ys))),
              Bits.touches_mask(rest, a, b, xs, ys)))),
        Bits.masked(a, b, Bits.get(xs, first), Bits.get(ys, second), Bits.touches(rest, xs, ys)))

def Bits.meet_mask(+a: Bool, +b: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>) ->
  {Bits.meet(Bits.mask(a, xs), Bits.mask(b, ys)) == Bool.and(a, Bool.and(b, Bits.meet(xs, ys))) : Bool}:
  match xs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(a, Bool.and(b, False{})), False{}, Bits.and_false(a, b))
    case x <> xs_rest:
      match ys:
        case Nil{}:
          Equal.sym(Bool, Bool.and(a, Bool.and(b, False{})), False{}, Bits.and_false(a, b))
        case y <> ys_rest:
          Equal.trans(Bool,
            Bool.or(Bool.and(Bool.and(a, x), Bool.and(b, y)), Bits.meet(Bits.mask(a, xs_rest), Bits.mask(b, ys_rest))),
            Bool.or(Bool.and(Bool.and(a, x), Bool.and(b, y)), Bool.and(a, Bool.and(b, Bits.meet(xs_rest, ys_rest)))),
            Bool.and(a, Bool.and(b, Bool.or(Bool.and(x, y), Bits.meet(xs_rest, ys_rest)))),
            Equal.cong(Bool, Bool, w => Bool.or(Bool.and(Bool.and(a, x), Bool.and(b, y)), w),
              Bits.meet(Bits.mask(a, xs_rest), Bits.mask(b, ys_rest)), Bool.and(a, Bool.and(b, Bits.meet(xs_rest, ys_rest))),
              Bits.meet_mask(a, b, xs_rest, ys_rest)),
            Bits.masked(a, b, x, y, Bits.meet(xs_rest, ys_rest)))

def Bits.select(keep: Bool, +n: Nat) -> Nat:
  match keep:
    case False{}:
      0n
    case True{}:
      n

def Bits.count_mask_false(+xs: List<&2, Bool>) -> {Bits.count(Bits.mask(False{}, xs)) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Bits.count_mask_false(rest)

def Bits.count_mask_true(+xs: List<&2, Bool>) -> {Bits.count(Bits.mask(True{}, xs)) == Bits.count(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(Nat, Nat, z => Nat.add(Bits.n(x), z), Bits.count(Bits.mask(True{}, rest)), Bits.count(rest), Bits.count_mask_true(rest))

def Bits.count_mask(keep: Bool, +xs: List<&2, Bool>) -> {Bits.count(Bits.mask(keep, xs)) == Bits.select(keep, Bits.count(xs)) : Nat}:
  match keep:
    case False{}:
      Bits.count_mask_false(xs)
    case True{}:
      Bits.count_mask_true(xs)

def Bits.select_single(n: Nat) -> {Bits.select(Nat.is_eq(n, 1n), n) == Bits.n(Nat.is_eq(n, 1n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}

def Bits.apart_union(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>,
  first: Bits.Holds(Bool.not(Bits.meet(xs, zs))), second: Bits.Holds(Bool.not(Bits.meet(ys, zs)))) ->
  Bits.Holds(Bool.not(Bits.meet(Bits.union(xs, ys), zs))):
  Bits.transport(Bool.not(Bool.or(Bits.meet(xs, zs), Bits.meet(ys, zs))), Bool.not(Bits.meet(Bits.union(xs, ys), zs)),
    Equal.cong(Bool, Bool, Bool.not, Bool.or(Bits.meet(xs, zs), Bits.meet(ys, zs)), Bits.meet(Bits.union(xs, ys), zs),
      Equal.sym(Bool, Bits.meet(Bits.union(xs, ys), zs), Bool.or(Bits.meet(xs, zs), Bits.meet(ys, zs)), Bits.meet_union(xs, ys, zs))),
    Bits.neither(Bits.meet(xs, zs), Bits.meet(ys, zs), first, second))

def Bits.apart_mask(+a: Bool, +b: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>,
  apart: Bits.Holds(Bool.not(Bool.and(a, Bool.and(b, Bits.meet(xs, ys)))))) ->
  Bits.Holds(Bool.not(Bits.meet(Bits.mask(a, xs), Bits.mask(b, ys)))):
  Bits.transport(Bool.not(Bool.and(a, Bool.and(b, Bits.meet(xs, ys)))), Bool.not(Bits.meet(Bits.mask(a, xs), Bits.mask(b, ys))),
    Equal.cong(Bool, Bool, Bool.not, Bool.and(a, Bool.and(b, Bits.meet(xs, ys))), Bits.meet(Bits.mask(a, xs), Bits.mask(b, ys)),
      Equal.sym(Bool, Bits.meet(Bits.mask(a, xs), Bits.mask(b, ys)), Bool.and(a, Bool.and(b, Bits.meet(xs, ys))), Bits.meet_mask(a, b, xs, ys))),
    apart)

def Bits.untouched_union_left(+pairs: Bits.Pairs, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>,
  first: Bits.Holds(Bool.not(Bits.touches(pairs, xs, zs))), second: Bits.Holds(Bool.not(Bits.touches(pairs, ys, zs)))) ->
  Bits.Holds(Bool.not(Bits.touches(pairs, Bits.union(xs, ys), zs))):
  Bits.transport(Bool.not(Bool.or(Bits.touches(pairs, xs, zs), Bits.touches(pairs, ys, zs))), Bool.not(Bits.touches(pairs, Bits.union(xs, ys), zs)),
    Equal.cong(Bool, Bool, Bool.not, Bool.or(Bits.touches(pairs, xs, zs), Bits.touches(pairs, ys, zs)), Bits.touches(pairs, Bits.union(xs, ys), zs),
      Equal.sym(Bool, Bits.touches(pairs, Bits.union(xs, ys), zs), Bool.or(Bits.touches(pairs, xs, zs), Bits.touches(pairs, ys, zs)),
        Bits.touches_union_left(pairs, xs, ys, zs))),
    Bits.neither(Bits.touches(pairs, xs, zs), Bits.touches(pairs, ys, zs), first, second))

def Bits.untouched_union_right(+pairs: Bits.Pairs, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>,
  first: Bits.Holds(Bool.not(Bits.touches(pairs, xs, ys))), second: Bits.Holds(Bool.not(Bits.touches(pairs, xs, zs)))) ->
  Bits.Holds(Bool.not(Bits.touches(pairs, xs, Bits.union(ys, zs)))):
  Bits.transport(Bool.not(Bool.or(Bits.touches(pairs, xs, ys), Bits.touches(pairs, xs, zs))), Bool.not(Bits.touches(pairs, xs, Bits.union(ys, zs))),
    Equal.cong(Bool, Bool, Bool.not, Bool.or(Bits.touches(pairs, xs, ys), Bits.touches(pairs, xs, zs)), Bits.touches(pairs, xs, Bits.union(ys, zs)),
      Equal.sym(Bool, Bits.touches(pairs, xs, Bits.union(ys, zs)), Bool.or(Bits.touches(pairs, xs, ys), Bits.touches(pairs, xs, zs)),
        Bits.touches_union_right(pairs, xs, ys, zs))),
    Bits.neither(Bits.touches(pairs, xs, ys), Bits.touches(pairs, xs, zs), first, second))

def Bits.untouched_mask(+pairs: Bits.Pairs, +a: Bool, +b: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>,
  apart: Bits.Holds(Bool.not(Bool.and(a, Bool.and(b, Bits.touches(pairs, xs, ys)))))) ->
  Bits.Holds(Bool.not(Bits.touches(pairs, Bits.mask(a, xs), Bits.mask(b, ys)))):
  Bits.transport(Bool.not(Bool.and(a, Bool.and(b, Bits.touches(pairs, xs, ys)))), Bool.not(Bits.touches(pairs, Bits.mask(a, xs), Bits.mask(b, ys))),
    Equal.cong(Bool, Bool, Bool.not, Bool.and(a, Bool.and(b, Bits.touches(pairs, xs, ys))), Bits.touches(pairs, Bits.mask(a, xs), Bits.mask(b, ys)),
      Equal.sym(Bool, Bits.touches(pairs, Bits.mask(a, xs), Bits.mask(b, ys)), Bool.and(a, Bool.and(b, Bits.touches(pairs, xs, ys))),
        Bits.touches_mask(pairs, a, b, xs, ys))),
    apart)

def Bits.unset_union(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +index: Nat,
  first: Bits.Holds(Bool.not(Bits.get(xs, index))), second: Bits.Holds(Bool.not(Bits.get(ys, index)))) ->
  Bits.Holds(Bool.not(Bits.get(Bits.union(xs, ys), index))):
  Bits.transport(Bool.not(Bool.or(Bits.get(xs, index), Bits.get(ys, index))), Bool.not(Bits.get(Bits.union(xs, ys), index)),
    Equal.cong(Bool, Bool, Bool.not, Bool.or(Bits.get(xs, index), Bits.get(ys, index)), Bits.get(Bits.union(xs, ys), index),
      Equal.sym(Bool, Bits.get(Bits.union(xs, ys), index), Bool.or(Bits.get(xs, index), Bits.get(ys, index)), Bits.get_union(xs, ys, index))),
    Bits.neither(Bits.get(xs, index), Bits.get(ys, index), first, second))

def Bits.unset_mask(+keep: Bool, +xs: List<&2, Bool>, +index: Nat, unset: Bits.Holds(Bool.not(Bool.and(keep, Bits.get(xs, index))))) ->
  Bits.Holds(Bool.not(Bits.get(Bits.mask(keep, xs), index))):
  Bits.transport(Bool.not(Bool.and(keep, Bits.get(xs, index))), Bool.not(Bits.get(Bits.mask(keep, xs), index)),
    Equal.cong(Bool, Bool, Bool.not, Bool.and(keep, Bits.get(xs, index)), Bits.get(Bits.mask(keep, xs), index),
      Equal.sym(Bool, Bits.get(Bits.mask(keep, xs), index), Bool.and(keep, Bits.get(xs, index)), Bits.get_mask(keep, xs, index))),
    unset)

def Bits.set_union(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +index: Nat, set: Bits.Holds(Bits.get(Bits.union(xs, ys), index))) ->
  Or(Bits.Holds(Bits.get(xs, index)), Bits.Holds(Bits.get(ys, index))):
  Bits.either(Bits.get(xs, index), Bits.get(ys, index),
    Bits.transport(Bits.get(Bits.union(xs, ys), index), Bool.or(Bits.get(xs, index), Bits.get(ys, index)), Bits.get_union(xs, ys, index), set))

def Bits.not_both_first(a: Bool, +b: Bool, +c: Bool, none: Bits.Holds(Bool.not(c))) -> Bits.Holds(Bool.not(Bool.and(a, Bool.and(b, c)))):
  match a:
    case False{}:
      Unit{}
    case True{}:
      match b:
        case False{}:
          Unit{}
        case True{}:
          none

def Bits.not_both_middle(a: Bool, +b: Bool, +c: Bool, none: Bits.Holds(Bool.not(b))) -> Bits.Holds(Bool.not(Bool.and(a, Bool.and(b, c)))):
  match a:
    case False{}:
      Unit{}
    case True{}:
      match b:
        case False{}:
          Unit{}
        case True{}:
          match none:

def Bits.apart_at_step(x: Bool, y: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>, index: Nat,
  apart: Bits.Holds(Bool.not(Bool.or(Bool.and(x, y), Bits.meet(xs, ys)))),
  rest: @previous: Nat -> Bits.Holds(Bool.not(Bits.meet(xs, ys))) -> Bits.Holds(Bool.not(Bool.and(Bits.get(xs, previous), Bits.get(ys, previous))))) ->
  Bits.Holds(Bool.not(Bool.and(Bits.get(Con{x, xs}, index), Bits.get(Con{y, ys}, index)))):
  match x y index:
    case False{} False{} 0n:
      Unit{}
    case False{} False{} 1n+previous:
      rest(previous, apart)
    case False{} True{} 0n:
      Unit{}
    case False{} True{} 1n+previous:
      rest(previous, apart)
    case True{} False{} 0n:
      Unit{}
    case True{} False{} 1n+previous:
      rest(previous, apart)
    case True{} True{} _:
      match apart:

def Bits.apart_at(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +index: Nat, apart: Bits.Holds(Bool.not(Bits.meet(xs, ys)))) ->
  Bits.Holds(Bool.not(Bool.and(Bits.get(xs, index), Bits.get(ys, index)))):
  match xs:
    case Nil{}:
      Unit{}
    case x <> xs_rest:
      match ys:
        case Nil{}:
          Bits.transport(True{}, Bool.not(Bool.and(Bits.get(Con{x, xs_rest}, index), False{})),
            Equal.sym(Bool, Bool.not(Bool.and(Bits.get(Con{x, xs_rest}, index), False{})), True{},
              Equal.cong(Bool, Bool, Bool.not, Bool.and(Bits.get(Con{x, xs_rest}, index), False{}), False{},
                Bits.and_false_right(Bits.get(Con{x, xs_rest}, index)))), Unit{})
        case y <> ys_rest:
          Bits.apart_at_step(x, y, xs_rest, ys_rest, index, apart,
            previous => rest => Bits.apart_at(xs_rest, ys_rest, previous, rest))

def Bits.le_holds(a: Nat, b: Nat, holds: Bits.Holds(Nat.is_le(a, b))) -> N.Natural.Le(a, b):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+bp:
      Unit{}
    case 1n+ap 0n:
      match holds:
    case 1n+ap 1n+bp:
      Bits.le_holds(ap, bp, holds)

def Bits.at_most_one(b: Bool) -> N.Natural.Le(Bits.n(b), 1n):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

def Bits.one_of(b: Bool, holds: Bits.Holds(b)) -> N.Natural.Le(1n, Bits.n(b)):
  match b:
    case False{}:
      match holds:
    case True{}:
      Unit{}

def Bits.none_of(b: Bool, holds: Bits.Holds(Bool.not(b))) -> N.Natural.Le(Bits.n(b), 0n):
  match b:
    case False{}:
      Unit{}
    case True{}:
      match holds:

def Bits.or_at_most(a: Bool, +b: Bool) -> N.Natural.Le(Bits.n(Bool.or(a, b)), Nat.add(Bits.n(a), Bits.n(b))):
  match a b:
    case False{} False{}:
      Unit{}
    case False{} True{}:
      Unit{}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      Unit{}

def Bits.first(a: Bool, +b: Bool, holds: Bits.Holds(a)) -> Bits.Holds(Bool.or(a, b)):
  match a:
    case False{}:
      match holds:
    case True{}:
      Unit{}

def Bits.second(a: Bool, +b: Bool, holds: Bits.Holds(b)) -> Bits.Holds(Bool.or(a, b)):
  match a:
    case False{}:
      holds
    case True{}:
      Unit{}

def Bits.not_and_first(a: Bool, +b: Bool, none: Bits.Holds(Bool.not(a))) -> Bits.Holds(Bool.not(Bool.and(a, b))):
  match a:
    case False{}:
      Unit{}
    case True{}:
      match none:

def Bits.not_first_of(a: Bool, +b: Bool, apart: Bits.Holds(Bool.not(Bool.and(a, b))), holds: Bits.Holds(b)) -> Bits.Holds(Bool.not(a)):
  match a:
    case False{}:
      Unit{}
    case True{}:
      Bits.never(b, holds, apart)

def Bits.apart_single(+x: Bool, +y: Bool, apart: Bits.Holds(Bool.not(Bool.and(x, y)))) ->
  Bits.Holds(Bool.not(Bits.meet(Con{x, Nil{}}, Con{y, Nil{}}))):
  Bits.transport(Bool.not(Bool.and(x, y)), Bool.not(Bool.or(Bool.and(x, y), False{})),
    Equal.cong(Bool, Bool, Bool.not, Bool.and(x, y), Bool.or(Bool.and(x, y), False{}),
      Equal.sym(Bool, Bool.or(Bool.and(x, y), False{}), Bool.and(x, y), Bits.or_false(Bool.and(x, y)))),
    apart)
