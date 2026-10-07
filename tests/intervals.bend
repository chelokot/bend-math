import Base
import ../Field.bend as K
import ../FieldAlgebra.bend as A
import ../Certificate.bend as C
import ../Intervals.bend as I

def two_intervals(~F: Kind(&2), ~field: K.Field<F>, +a: F, +x: F, +y: F, +z: F, +w: F, +b: F,
  +ax: A.Algebra.le(~F, ~field, a, x), +xy: A.Algebra.le(~F, ~field, x, y), +yz: A.Algebra.le(~F, ~field, y, z),
  +zw: A.Algebra.le(~F, ~field, z, w), +wb: A.Algebra.le(~F, ~field, w, b)) ->
  A.Algebra.le(~F, ~field, A.Algebra.add(~F, ~field, I.Intervals.minus(~F, ~field, y, x), A.Algebra.add(~F, ~field, I.Intervals.minus(~F, ~field, w, z), A.Algebra.zero(~F, ~field))),
    I.Intervals.minus(~F, ~field, b, a)):
  +az: A.Algebra.le(~F, ~field, a, z) = I.Intervals.le_trans(~F, ~field, a, y, z, I.Intervals.le_trans(~F, ~field, a, x, y, ax, xy), yz)
  +yb: A.Algebra.le(~F, ~field, y, b) = I.Intervals.le_trans(~F, ~field, y, w, b, I.Intervals.le_trans(~F, ~field, y, z, w, yz, zw), wb)
  I.Intervals.packed(~F, ~field, a, b, I.Interval{x, y} <> I.Interval{z, w} <> Nil{},
    I.Intervals.le_trans(~F, ~field, a, z, b, az, I.Intervals.le_trans(~F, ~field, z, w, b, zw, wb)),
    C.Both{C.Both{ax, C.Both{xy, yb}}, C.Both{C.Both{az, C.Both{zw, wb}}, Unit{}}},
    C.Both{C.Both{Inl{yz}, Unit{}}, C.Both{Unit{}, Unit{}}})
