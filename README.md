# The Prime Spectrum of Rings of Integer-Coefficient Power Series on the Disk

Jon Bannon and David Feldman

This repository contains two companion papers and their complete Lean 4
formalization.

**Paper I** — *Integer Coefficients Power Series with Prescribed Zero Sets*
(`integer_weierstrass_18.tex`): a discrete effective divisor on the open unit
disk 𝔻 is the zero divisor of a holomorphic function with integer Taylor
coefficients if and only if it is invariant under complex conjugation; with
Gaussian-integer coefficients the invariance hypothesis is unnecessary.
Ring-theoretic consequences for ℛ = ℤ[i][[z]] ∩ 𝒪(𝔻) include the unit
characterization, the isomorphism ℛ/𝔫₀ ≅ ℤ[i], and the order isomorphism
between the primes over 𝔫₀ and Spec ℤ[i].

**Paper II** — *The Prime Spectrum of Rings of Integer-Coefficient Power
Series on the Disk* (`integer_power_series_spectrum_v2.tex`): the prime and
maximal spectra of ℛ_ℝ = ℤ[[z]] ∩ 𝒪(𝔻). Results include a trichotomy for
maximal ideals; the classification of primes containing z or a nonzero
integer; the p-adic evaluation primes Q_p with ℛ_ℝ/Q_p ≅ ℤ_p, which show
that Spec(ℛ_ℝ) ∖ 𝔓₁ strictly contains {(0), (z)} ∪ {(p)} ∪ {(z,p)}; an
analytic invariant on 𝔓₁ with a partition property; an injection from
ultrafilters on real-supported admissible divisors into 𝔓₁ via an
ultraproduct construction; point-evaluation ideals; and a conditional
Bézout theorem for functions with disjoint divisors and coprime constant
terms.

## Formalization

Every numbered theorem, proposition, lemma, and corollary of both papers is
formally verified in Lean 4 against Mathlib (toolchain in `lean-toolchain`).
The libraries:

- `RequestProject/` — the disk ring 𝒪(𝔻), the coefficient-restricted rings,
  and the ring-theoretic results of Paper I, including the fiber
  correspondence with Spec ℤ[i] (`FiberPrimes.lean`).
- `WeierstrassFormalization/` — the realization theorems of Paper I:
  elementary factors, paired enumeration and rounding, divisor control, and
  the integer and Gaussian realization theorems.
- `SpectrumFormalization/` — Paper II: the trichotomy, the prime
  classification (`PrimesOutside.lean`), the unit-quotient lemma
  (`UnitQuotient.lean`), the partition property (`Partition.lean`), the
  ultraproduct construction and its trace (`Ultraproduct.lean`,
  `UltraTrace.lean`), the p-adic evaluation primes (`PadicEval.lean`),
  point evaluation (`PointEval.lean`), and the corrected Bézout theorem
  with its sharpness (`Bezout.lean`).

The development contains no `sorry`, `admit`, extra axioms,
`@[implemented_by]`, or `native_decide`. `SpectrumFormalization/AxiomCheck.lean`
is part of the build and audits every headline declaration with
`#print axioms`; each reports exactly `propext, Classical.choice, Quot.sound`.

`FORMALIZATION_STATUS.md` and `SEQUEL_FORMALIZATION_STATUS.md` map the
papers' statements to Lean declarations. The conjecture and open questions
of Paper II's final section are not formalized.

## Building

```
lake exe cache get
lake build
```

## Provenance

The Lean development was produced by
[Aristotle](https://aristotle.harmonic.fun) (Harmonic) executing work orders
prepared by the authors with Claude (Anthropic); see `ARISTOTLE.md` for
attribution and `ARISTOTLE_SUMMARY.md` for the dated run reports.
