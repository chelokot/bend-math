# bend-math

Formally checked exact mathematics for [Bend 2](https://github.com/bendlang/bend).

This library is under construction. It has definitions of integers, rationals,
and general Cauchy sequences of rationals. It does **not** yet prove that these
structures form the complete ordered field of real numbers, or formalize the
square-packing problem. A green CI run means only that the laws currently
declared in `LAWS.bend` have proofs. It is not a completeness claim.

The intended dependency chain is integers, rationals, general real numbers,
ordered-field laws, roots and exact inequalities, then the lemmas needed by
[square-packing-archive](https://github.com/chelokot/square-packing-archive).
The final real-number model must cover arbitrary real coordinates, not just
named computable constants. Floating-point values and unproved field axioms
cannot substitute for that model.

`Real.bend` currently represents a rational-valued regular Cauchy sequence,
with equality defined by two directed cross-precision bounds. Bend checks that
zero is a valid real and that this equality is reflexive and symmetric.
Transitivity, field operations, order, completeness, and compatibility with
the rational quotient are still open work. The checked definitions alone do
not license any theorem about square packing.

The construction is informed by [Mathlib's Cauchy reals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Basic/Real/Basic.html)
and the published [`bend.how` examples](https://bend.how/lib/). Their current
`Real` example supports a few named recipes rather than arbitrary reals. No
third-party source code is included here.

Check the current laws with Bend 2.0.25 at commit
`26659268dbdf411696bf90d28e722783dceae0f8`:

```sh
bun /path/to/bend/bend2/main.ts PROOF.bend --check-only
```

`LAWS.bend` is the review boundary: adding a theorem requires writing its
statement there and a proof in `PROOF.bend`. Every file imported by the proof
gate is checked. Unsafe recursion, foreign effects and unfilled laws are not
acceptable for mathematical proofs.
