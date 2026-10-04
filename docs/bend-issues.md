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
