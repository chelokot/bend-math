# Bend issues found while building this library

These are not reported upstream yet. Each entry records the Bend revision, a
minimal reproduction, and the workaround used here.

## 1. A lambda inside a type fails `--verdict`

Bend 2.0.35 (`79df8d9c`). The TypeScript checker accepts a sample type whose
sequence is written as an inline lambda, but the kernel rejects the conversion
between `λx6 => (λ+x7 => body) x6` and an annotated η-expansion of the same
function:

```bend
def add_sample(-f: Nat -> Q.Rational, -g: Nat -> Q.Rational, +n: Nat, +m: Nat,
  x: Sample<f, 1n+n, 1n+m>, y: Sample<g, 1n+n, 1n+m>) ->
  Sample<(k => Q.Rational.add(f(1n+k), g(1n+k))), n, m>
```

`--check-only` passes; `--verdict` prints the TypeScript/kernel mismatch.

Workaround: name the sequence as its own def (`Real.add_approximations`).

## 2. An instance of a template-generic proof fails `--verdict`

Bend 2.0.35 (`79df8d9c`). A generic lemma over the field record checks under
`--verdict`, and `RationalField.field()` checks too, but the instance
`zero_add_le(~Q.Rational, ~F.RationalField.field(), Q.Rational.one())` fails
in the kernel with `expected: an annotated term` on an inlined
`Rational.distributive_scaled_structural` step.

Workaround: none needed. The generic theorem and the model are checked
separately, which is what a statement over every ordered field requires.

## 3. `--verdict` copies every template into each root that reaches it

Bend 2.0.35 (`79df8d9c`). `safe_book` checks each def at its own opaque
constants for its `~` parameters, and a call `B(~A~F, …)` from root `A`
emits a fresh copy of `B` and of everything `B` reaches. The kernel input is
therefore the sum over defs of their transitive closure. In
`square-packing-archive`, the s(6) lower bound is 2.4MB of Bend, and its
kernel input is 518MB: `Stromquist.extra_base` alone appears 18 times at 4MB.

Workaround: merge defs that share heavy dependencies into one generic def
(one `center` over its row indices instead of six), and give the check
enough memory.

## 4. Kernel names grow by one character per instance

Bend 2.0.35 (`79df8d9c`). `fresh` in `bend2/safe.ts` appends `_` until a
name is free, so the k-th instance of a def is named with k underscores and
the names cost quadratic space in the number of instances (and the loop
quadratic time). In the 518MB input above, 295MB is underscores of `qvv_…`
names; `FieldRing.of_nat` has about 300 instances. A counter per base name
would keep names short.

Workaround: none on the library side. The kernel check of that book peaks
at about 17GB in `bun` and 19GB in the kernel, which runs while `bun` still
holds its memory.
