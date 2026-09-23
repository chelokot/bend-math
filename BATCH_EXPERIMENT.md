# Batched Cauchy queries

`BatchReal.bend` tests a replacement for a reusable approximation function.
Each query returns two rational approximations and a checked bound between
them. `BatchReal.add` is checked by Bend 2.0.25 and consumes each source query
only once.

This is not yet a real-number model. `BatchReal.bad` passes the local bound
for every query because it returns the same rational twice. Its diagonal
answers are zero at precision zero and three at precision one. The checked
theorem `BatchReal.bad_not_regular` shows those answers violate the required
cross-precision bound. The missing invariant is consistency between
*different* queries, not the bound within a single query.

Run `bun /path/to/bend/bend2/main.ts BatchReal.bend --check-only` to check
both the addition construction and the counterexample. Do not use
`BatchReal` as a replacement for `Real` in any ordered-field or completeness
claim without a checked global coherence condition.
