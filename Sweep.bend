import Base
import ./Field.bend as K
import ./FieldAlgebra.bend as A
import ./FieldOrder.bend as O
import ./Certificate.bend as C

def Sweep.Clean(-F: Kind(&2), -field: K.Field<F>, +a: F, +b: F, list: List<&2, F>) -> Kind(&2):
  match list:
    case Nil{}:
      Unit
    case +point <> rest:
      C.Certificate.Both<Either<&2, &2, K.Field.le(F, field)(point, a), K.Field.le(F, field)(b, point)>, Sweep.Clean(F, field, a, b, rest)>

def Sweep.Member(-F: Kind(&2), -field: K.Field<F>, +point: F, list: List<&2, F>) -> Kind(&2):
  match list:
    case Nil{}:
      Empty
    case +other <> rest:
      Either<&2, &2, C.Certificate.Both<K.Field.le(F, field)(point, other), K.Field.le(F, field)(other, point)>, Sweep.Member(F, field, point, rest)>

def Sweep.Members(-F: Kind(&2), -field: K.Field<F>, +pending: List<&2, F>, list: List<&2, F>) -> Kind(&2):
  match list:
    case Nil{}:
      Unit
    case +point <> rest:
      C.Certificate.Both<Sweep.Member(F, field, point, pending), Sweep.Members(F, field, pending, rest)>

def Sweep.Marked(-F: Kind(&2), -field: K.Field<F>, +a: F, +b: F, +pending: List<&2, F>, list: List<&2, F>) -> Kind(&2):
  match list:
    case Nil{}:
      Unit
    case +point <> rest:
      C.Certificate.Both<Either<&2, &2, Either<&2, &2, K.Field.le(F, field)(point, a), K.Field.le(F, field)(b, point)>, Sweep.Member(F, field, point, pending)>,
        Sweep.Marked(F, field, a, b, pending, rest)>

def Sweep.members_more(~F: Kind(&2), ~field: K.Field<F>, +other: F, +pending: List<&2, F>, +list: List<&2, F>,
  +members: Sweep.Members(F, field, pending, list)) -> Sweep.Members(F, field, other <> pending, list):
  match list members:
    case Nil{} Unit{}:
      Unit{}
    case +point <> rest C.Both{+member, +others}:
      C.Both{Inr{member}, Sweep.members_more(~F, ~field, other, pending, rest, others)}

def Sweep.members_self(~F: Kind(&2), ~field: K.Field<F>, +list: List<&2, F>) -> Sweep.Members(F, field, list, list):
  match list:
    case Nil{}:
      Unit{}
    case +point <> rest:
      C.Both{Inl{C.Both{K.Field.le_reflexive(F, field)(point), K.Field.le_reflexive(F, field)(point)}},
        Sweep.members_more(~F, ~field, point, rest, rest, Sweep.members_self(~F, ~field, rest))}

def Sweep.marked_members(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +pending: List<&2, F>, +list: List<&2, F>,
  +members: Sweep.Members(F, field, pending, list)) -> Sweep.Marked(F, field, a, b, pending, list):
  match list members:
    case Nil{} Unit{}:
      Unit{}
    case +point <> rest C.Both{+member, +others}:
      C.Both{Inr{member}, Sweep.marked_members(~F, ~field, a, b, pending, rest, others)}

def Sweep.clean(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +list: List<&2, F>, +marked: Sweep.Marked(F, field, a, b, Nil{}, list)) ->
  Sweep.Clean(F, field, a, b, list):
  match list marked:
    case Nil{} Unit{}:
      Unit{}
    case +point <> rest C.Both{Inl{+outside}, +others}:
      C.Both{outside, Sweep.clean(~F, ~field, a, b, rest, others)}
    case +point <> rest C.Both{Inr{never}, +others}:
      Empty.absurd(Sweep.Clean(F, field, a, b, point <> rest), never)

def Sweep.outside_of(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +split: F, +point: F,
  outside: Either<&2, &2, A.Algebra.le(~F, ~field, split, a), A.Algebra.le(~F, ~field, b, split)>,
  +below: A.Algebra.le(~F, ~field, point, split), +above: A.Algebra.le(~F, ~field, split, point)) ->
  Either<&2, &2, A.Algebra.le(~F, ~field, point, a), A.Algebra.le(~F, ~field, b, point)>:
  match outside:
    case Inl{left}:
      Inl{K.Field.le_transitive(F, field)(point, split, a, below, left)}
    case Inr{right}:
      Inr{K.Field.le_transitive(F, field)(b, split, point, right, above)}

def Sweep.skip(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +split: F, +pending: List<&2, F>, +list: List<&2, F>,
  +outside: Either<&2, &2, A.Algebra.le(~F, ~field, split, a), A.Algebra.le(~F, ~field, b, split)>,
  +marked: Sweep.Marked(F, field, a, b, split <> pending, list)) -> Sweep.Marked(F, field, a, b, pending, list):
  match list marked:
    case Nil{} Unit{}:
      Unit{}
    case +point <> rest C.Both{Inl{+known}, +others}:
      C.Both{Inl{known}, Sweep.skip(~F, ~field, a, b, split, pending, rest, outside, others)}
    case +point <> rest C.Both{Inr{Inl{C.Both{+below, +above}}}, +others}:
      C.Both{Inl{Sweep.outside_of(~F, ~field, a, b, split, point, outside, below, above)}, Sweep.skip(~F, ~field, a, b, split, pending, rest, outside, others)}
    case +point <> rest C.Both{Inr{Inr{+member}}, +others}:
      C.Both{Inr{member}, Sweep.skip(~F, ~field, a, b, split, pending, rest, outside, others)}

def Sweep.left(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +split: F, +pending: List<&2, F>, +list: List<&2, F>,
  +before: A.Algebra.le(~F, ~field, split, b), +marked: Sweep.Marked(F, field, a, b, split <> pending, list)) ->
  Sweep.Marked(F, field, a, split, pending, list):
  match list marked:
    case Nil{} Unit{}:
      Unit{}
    case +point <> rest C.Both{Inl{Inl{+left}}, +others}:
      C.Both{Inl{Inl{left}}, Sweep.left(~F, ~field, a, b, split, pending, rest, before, others)}
    case +point <> rest C.Both{Inl{Inr{+right}}, +others}:
      C.Both{Inl{Inr{K.Field.le_transitive(F, field)(split, b, point, before, right)}}, Sweep.left(~F, ~field, a, b, split, pending, rest, before, others)}
    case +point <> rest C.Both{Inr{Inl{C.Both{+below, +above}}}, +others}:
      C.Both{Inl{Inr{above}}, Sweep.left(~F, ~field, a, b, split, pending, rest, before, others)}
    case +point <> rest C.Both{Inr{Inr{+member}}, +others}:
      C.Both{Inr{member}, Sweep.left(~F, ~field, a, b, split, pending, rest, before, others)}

def Sweep.right(~F: Kind(&2), ~field: K.Field<F>, +a: F, +b: F, +split: F, +pending: List<&2, F>, +list: List<&2, F>,
  +after: A.Algebra.le(~F, ~field, a, split), +marked: Sweep.Marked(F, field, a, b, split <> pending, list)) ->
  Sweep.Marked(F, field, split, b, pending, list):
  match list marked:
    case Nil{} Unit{}:
      Unit{}
    case +point <> rest C.Both{Inl{Inl{+left}}, +others}:
      C.Both{Inl{Inl{K.Field.le_transitive(F, field)(point, a, split, left, after)}}, Sweep.right(~F, ~field, a, b, split, pending, rest, after, others)}
    case +point <> rest C.Both{Inl{Inr{+right}}, +others}:
      C.Both{Inl{Inr{right}}, Sweep.right(~F, ~field, a, b, split, pending, rest, after, others)}
    case +point <> rest C.Both{Inr{Inl{C.Both{+below, +above}}}, +others}:
      C.Both{Inl{Inl{below}}, Sweep.right(~F, ~field, a, b, split, pending, rest, after, others)}
    case +point <> rest C.Both{Inr{Inr{+member}}, +others}:
      C.Both{Inr{member}, Sweep.right(~F, ~field, a, b, split, pending, rest, after, others)}

def Sweep.cases_of(~F: Kind(&2), ~field: K.Field<F>, +x: F, +y: F, -Goal: Type,
  order: Or(A.Algebra.le(~F, ~field, x, y), A.Algebra.le(~F, ~field, x, y) -> Empty),
  below: A.Algebra.le(~F, ~field, x, y) -> Goal, above: A.Algebra.le(~F, ~field, y, x) -> Goal) -> Goal:
  match order:
    case Inl{yes}:
      below(yes)
    case Inr{no}:
      above(O.FieldOrder.le_of_lt(~F, ~field, y, x, no))
