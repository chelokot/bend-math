import Base
import ../Ring.bend as R

def same_normal_form() ->
  {R.Ring.norm(R.Product{R.Sum{R.Atom{0n}, R.Atom{1n}}, R.Next{R.Atom{2n}}}) ==
   R.Ring.norm(R.Sum{R.Sum{R.Product{R.Atom{2n}, R.Atom{1n}}, R.Atom{1n}}, R.Product{R.Next{R.Atom{2n}}, R.Atom{0n}}}) : R.Ring.Poly}:
  {==}

def scaled_left_cross(+p: Nat, +n: Nat, +a: Nat, +b: Nat, +d: Nat) ->
  {Nat.add(Nat.mul(p, Nat.mul(b, d)), Nat.mul(Nat.add(Nat.mul(n, d), 0n), a)) ==
   Nat.mul(d, Nat.add(Nat.mul(p, b), Nat.mul(n, a))) : Nat}:
  R.Ring.equal(R.Value{p, R.Value{n, R.Value{a, R.Value{b, R.Value{d, R.NoValues{}}}}}},
    R.Sum{R.Product{R.Atom{0n}, R.Product{R.Atom{3n}, R.Atom{4n}}}, R.Product{R.Sum{R.Product{R.Atom{1n}, R.Atom{4n}}, R.Constant{0n}}, R.Atom{2n}}},
    R.Product{R.Atom{4n}, R.Sum{R.Product{R.Atom{0n}, R.Atom{3n}}, R.Product{R.Atom{1n}, R.Atom{2n}}}},
    {==})
