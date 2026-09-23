# Batched Cauchy queries

`BatchReal.bend` tests a replacement for a reusable approximation function.
Each query returns two rational approximations and a checked bound between
them. `BatchReal.add` is checked by Bend 2.0.25 and consumes each source query
only once.

The naive version is not a real-number model. `BatchReal.bad` passes the local bound
for every query because it returns the same rational twice. Its diagonal
answers are zero at precision zero and three at precision one. The checked
theorem `BatchReal.bad_not_regular` shows those answers violate the required
cross-precision bound. The missing invariant is consistency between
*different* queries, not the bound within a single query.

`CoherentBatchReal.bend` adds an erased canonical rational sequence. Every
query carries structural equalities tying its answers to the canonical
sequence. Bend checks that this implies the ordinary Cauchy bound, excludes
the previous bad sequence, and permits addition that respects the defined
cross-precision equality. Rational constants have checked embeddings;
equality is reflexive and symmetric.

This stronger representation is still experimental. There is no checked
constructor from an arbitrary ordinary regular Cauchy function to its
certified batch oracle. Equality transitivity, multiplication, order and
completeness are also unproved. In particular, these checked laws do not
establish that the carrier contains every real number.

The carrier still has kind `Type`. The direct term `add(x, x)` for an arbitrary
variable `x` is rejected because it consumes `x` twice. A separately
implemented doubling operation might be possible, but would not itself give
ordinary reusable field elements. This is another obligation before the
representation can support the intended mathematics.

Run `bun /path/to/bend/bend2/main.ts CoherentBatchReal.bend --check-only`
to check both experiments. Do not use either representation in an
ordered-field or completeness claim before the remaining obligations are
proved.
