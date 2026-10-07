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
representations give equivalent reals, real equality is an equivalence
relation, and the reals with addition and negation form an abelian group up
to that equality. Multiplication, order,
completeness, and compatibility with the rational quotient are still open
work. The checked definitions alone do not license any theorem about square
packing.

Bend never copies a function, so a proof cannot apply the approximation
function of a real a second time after it has gone into a new sequence. The
regularity field therefore returns its two approximations as ordinary rational
values, together with equalities to the function's results. Proofs compute
with those copies and mention the function only inside types, where it may
occur freely.

`Field.bend` states an ordered field as a record that theorems take as a `~`
template, so its operations and axioms may be used any number of times. Every
axiom is phrased through the order, with equality meaning `a ≤ b` and `b ≤ a`.
The trivial one-element structure therefore models the record, which lets the
proven kernel check generic theorems, and `RationalField.bend` proves that the
rationals satisfy every axiom. A theorem proved for every such field holds for
the real numbers in particular.

`FieldAlgebra.bend` derives the equivalence, congruence and cancellation laws
of that equality, and `FieldRing.bend` proves ring identities with negation
over any such field. `FieldRing.equal` splits both sides into positive and
negative polynomials, reuses the `Ring.bend` normal form, and its soundness is
checked for every field. `FieldOrder.bend` adds the order facts the packing
proofs use: adding inequalities, negation reversing the order, and the
embedding of the naturals being nonnegative and monotone. A strict inequality
`a < b` is a function, so a proof can use it once; `FieldOrder.Strict` stores it
as a decided comparison, which is Data, and `FieldOrder.lt_of` turns it back
into `a < b` as often as needed.

`Certificate.bend` proves inequalities of the form `0 ≤ goal` from facts
`0 ≤ fact` and equations `equation = 0`. A certificate writes `(1 + d) · goal`
as a sum of natural multiples of fact products times squares, plus polynomial
multiples of equations; Bend checks the identity with `FieldRing.equal` and
each term's sign. `tools/certificate.py` searches for such a certificate with
a linear program over the products reduced modulo the equations, solved
exactly on the support that HiGHS (from SciPy, when installed) picks with the
smallest coefficients, and prints it as Bend terms:

```sh
python3 tools/certificate.py problem.json
```

where `problem.json` lists `names`, `facts`, `equations`, `goal` and optional
`squares`, each as a polynomial over the names.

`Bits.bend` counts and combines lists of decided facts: `Bits.Holds(b)` turns
a Boolean into a copyable proof, and its lemmas bound the number of set bits
and combine bit masks, so a finite case analysis is a computation on Booleans.

`Intervals.bend` bounds the total length of intervals in `[a, b]` whose
interiors are pairwise disjoint by `b − a`. It is the one-dimensional step of
area arguments: the vertical sections of interior-disjoint squares at one
abscissa are such intervals.

`Ring.bend` proves polynomial identities over `Nat`. A proof writes both sides
as expression trees over a list of values; `Ring.equal` normalizes them to
sorted monomials and is accepted only when the normal forms are identical. Its
soundness theorem is checked, so a wrong identity cannot pass, and the failing
check prints the two different normal forms.

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
2. Lift multiplication, order and limits to Cauchy representations.
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
