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

`Real.bend` represents a rational-valued regular Cauchy sequence, with
equality defined by two directed cross-precision bounds. Bend checks that every
rational has a constant real representation, equivalent rational
representations give equivalent reals, real equality is reflexive and
symmetric, and any two reals have a sum. Transitivity, multiplication, order,
completeness, and compatibility with the rational quotient are still open
work. The checked definitions alone do not license any theorem about square
packing.

Bend never copies a function, so a proof cannot apply the approximation
function of a real a second time after it has gone into a new sequence. The
regularity field therefore returns its two approximations as ordinary rational
values, together with equalities to the function's results. Proofs compute
with those copies and mention the function only inside types, where it may
occur freely.

`Rational.bend` stores a numerator as the difference of two naturals and a
strictly positive denominator as one plus a natural. Different records can
denote the same rational; equality and order use cross multiplication. This
keeps the proof obligations over exact natural-number arithmetic.

The next proof boundaries are:

1. Finish the ordered-ring laws for `Integer` and the ordered-field laws for
   `Rational`. Rational equality and order are transitive, addition and
   multiplication are associative and commutative, and addition respects
   cross-multiplication equality. Multiplication also respects equality, and
   both distributive laws are proved. A nonzero rational has a checked
   multiplicative inverse, including compatibility with equivalent
   representations. Products of nonnegative rationals are nonnegative.
2. Prove `Real.Eq` transitive, show that addition respects it, and lift
   multiplication, order and limits to Cauchy representations.
3. Prove completeness and construct square roots with their defining laws.
4. Formalize only the extra exact inequalities required by the packing
   theorems. The [archive's Bend migration branch](https://github.com/chelokot/square-packing-archive/tree/rewrite/bend2-formal-archive)
   will then pin a checked revision of this package.

The construction is informed by [Mathlib's Cauchy reals](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Basic/Real/Basic.html)
and the published [`bend.how` examples](https://bend.how/lib/). Their current
`Real` example supports a few named recipes rather than arbitrary reals. No
third-party source code is included here.

Check the current laws with Bend 2.0.35 at commit
`79df8d9c40722ee9507a1e253f283b51025f9d6c`. `--verdict` rechecks every proof
with Bend's kernel, which is proved in Lean and needs Lean 4.34.0:

```sh
bun /path/to/bend/bend2/main.ts PROOF.bend --verdict
```

`LAWS.bend` is the review boundary: adding a theorem requires writing its
statement there and a proof in `PROOF.bend`. Every file imported by the proof
gate is checked. Unsafe recursion, foreign effects and unfilled laws are not
acceptable for mathematical proofs.
