# Sequel formalization status

This documents the Lean formalization of the sequel paper
*The Prime Spectrum of Rings of Integer-Coefficient Power Series on the Disk*
(Bannon–Feldman), the companion to *Integer Coefficients Power Series with
Prescribed Zero Sets* (Paper I).

The new development lives in `SpectrumFormalization/` and **builds on the
Paper I formalization** (`RequestProject/`, `WeierstrassFormalization/`): it
reuses the concrete disk ring `𝒪(𝔻) = OD`, the Gaussian ring `ℛ = Rsub`, the
Taylor-coefficient calculus, the unit characterization, and the factorization
results established there.

Every declaration listed below builds with **no `sorry`/`admit`/`axiom`** and the
headline theorems depend only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound`.

## The rings and shared infrastructure

* `SpectrumFormalization/RealRing.lean` — the sequel's ring
  `ℛ_ℝ = ℤ[[z]] ∩ 𝒪(𝔻)`, defined as `RRsub`, the image in `OD` of the functions
  with integer Taylor coefficients. A generic "coefficients in a subring `S ⊆ ℂ`"
  predicate `IsSubringCoeffs` unifies the integer (`ℛ_ℝ`) and Gaussian (`ℛ`)
  cases; `coeffSubring` packages it as a subring of `diskAnalytic`.
* `SpectrumFormalization/PowerSeriesFun.lean` — `psFun`, the holomorphic function
  on `𝔻` defined by a bounded coefficient sequence, with its Taylor coefficients,
  analyticity, and summation identities; and `analyticOnNhd_𝔻_hasSum`
  (value = Taylor sum on `𝔻`).
* `SpectrumFormalization/CoeffHom.lean` — the well-defined Taylor coefficients on
  `OD` (`ODtaylorCoeff`), and the **injective-ready coefficient ring
  homomorphism** `coeffHom : ℛ_ℝ → ℤ⟦z⟧` (the Cauchy product for Taylor
  coefficients makes it multiplicative).
* `SpectrumFormalization/ModP.lean` — the **reduction homomorphism**
  `redHom p : ℛ_ℝ → 𝔽ₚ⟦z⟧`, proved **surjective** with kernel exactly `(p)`. This
  is the identification `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧` that drives the trichotomy.

## Results formalized

### Point-evaluation ideals (`SpectrumFormalization/PointEval.lean`)

For `a ∈ 𝔻`, `ev_a : f ↦ f(a)` and `P_a = ker(ev_a)`.

* `pointIdealRR_isPrime`, `pointIdealR_isPrime` — **Primeness**: `P_a` is prime in
  `ℛ_ℝ` and in `ℛ` for every `a ∈ 𝔻`.
* `pointIdealRR_isMaximal_real` — **Maximality for real points**: for real
  `a ∈ 𝔻`, `a ≠ 0`, `P_a` is maximal in `ℛ_ℝ` (with `ℛ_ℝ/P_a ≅ ℝ`), via the
  bounded radix expansion `exists_radix_real`.
* `pointIdealR_isMaximal` — **Maximality in `ℛ`**: for `a ∈ 𝔻`, `a ≠ 0`, `P_a` is
  maximal in `ℛ` (with `ℛ/P_a ≅ ℂ`), via the Gaussian radix expansion
  `exists_radix_gaussian`.
  * *Note.* The paper states the maximality "for each `a ∈ 𝔻`"; the case `a = 0`
    is genuinely excluded (there `ev_0` has image `ℤ` resp. `ℤ[i]`, so
    `P_0 = 𝔫₀` is not maximal). The formalized statements make the `a ≠ 0`
    hypothesis explicit, matching the radix-expansion proof.

### Trichotomy of maximal ideals (`SpectrumFormalization/Spectrum.lean`)

* `zElt`, `ev0RR` — the element `z ∈ ℛ_ℝ` and the constant-term ring
  homomorphism `ev₀ : ℛ_ℝ → ℤ`.
* `trichotomy` — **Proposition (trichotomy of maximal ideals)**: every maximal
  ideal `M` of `ℛ_ℝ` either contains `z` (type (i)), or contains no nonzero
  integer and not `z` (type (iii)); the intermediate "type (ii)" (an integer
  `|n| > 1` in `M` but `z ∉ M`) **cannot occur**. The engine
  `zElt_mem_of_prime_mem` uses `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`: an element of `M` with unit
  constant term would be a unit mod `p`, forcing `1 ∈ M`.

### Units and the unit-quotient lemma (`SpectrumFormalization/Units.lean`, `UnitQuotient.lean`, `Shift.lean`)

* `IsSubringCoeffs.inv` — generic reciprocal-coefficient lemma (the reciprocal of
  a nowhere-vanishing function with coefficients in a subring `S` and unit
  constant term again has coefficients in `S`).
* `units_RRsub` — **Proposition `prop:units` (real case)**: `x ∈ ℛ_ℝ` is a unit
  iff it is a unit of `𝒪(𝔻)` (nowhere vanishing on `𝔻`) and its constant term is
  a unit of `ℤ` (i.e. `±1`). (Recalled from Paper I; here proved directly for
  `ℛ_ℝ`.)
* `isUnit_iff_isUnit_subtype_of_ev0_eq_one` — **`prop:interesting` (ii)**: an
  element `1 + zF` is a unit iff it is nowhere vanishing on `𝔻`.
* `exists_zElt_factor` (`Shift.lean`) — **division by `z`**: an element of `ℛ_ℝ`
  with constant term `0` is divisible by `z` (the coefficient-shift operation,
  built from `dslope`).
* `ODorder`, `SameZeroDivisor`, `unit_quotient` (`UnitQuotient.lean`) —
  **the unit-quotient lemma (`lem:unitquotient` = `prop:interesting` (iv))**: two
  elements of `ℛ_ℝ` with constant term `1` and the same zero divisor on `𝔻`
  differ by a unit of `ℛ_ℝ`. Proved via the meromorphic zero/pole extraction of
  Paper I (`divisor_mul_inv_eq_zero`, `factor_of_divisor_zero`) together with the
  integer-coefficient triangular recursion `IsSubringCoeffs.of_mul_factor`.

## Newly formalized (extension using the v19 manuscript)

The following were added in a later pass, drawing on the extended (v19) manuscript
which develops the prime-ideal structure in more detail. All build with no
`sorry`/`admit`/`axiom` and depend only on `propext`, `Classical.choice`,
`Quot.sound`.

* `SpectrumFormalization/DomainFacts.lean` — **`𝒪(𝔻)` and `ℛ_ℝ` are integral
  domains** (`OD_isDomain`, `RRsub_isDomain`, via the identity theorem for the
  connected disk); **`coeffHom` is injective** (`coeffHom_injective`,
  `eq_zero_of_intCoeff_eq_zero`); and **`ℛ_ℝ/(z) ≅ ℤ`** in the form
  `ker_ev0RR : RingHom.ker ev0RR = (z)`.
* `SpectrumFormalization/PrimesOutside.lean` — the ideals `(p)` are **prime but
  not maximal** (`span_p_isPrime`, `span_p_not_isMaximal`, via `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`);
  the ideals `(z, p)` are **maximal** (`span_zp_isMaximal`, via `ℛ_ℝ/(z,p) ≅ 𝔽ₚ`);
  `(0)` and `(z)` are **prime** (`bot_isPrime`, `span_zElt_isPrime`);
  **complete classification of primes containing `z`** (`prime_of_z_mem`: such a
  prime is `(z)` or `(z, p)`), via the `ℛ_ℝ/(z) ≅ ℤ` correspondence and the
  primes of `ℤ` (`int_prime_ideal`); the **type-(i) maximal ideals are exactly
  the `(z, p)`** (`typeI_maximal_iff`); and a prime with `z ∉ P` **containing a
  rational prime `p` equals `(p)`** (`eq_span_p_of_prime_mem`, via the DVR fact
  `powerSeries_field_prime_eq_bot_of_X_not_mem`). *Correction to the paper:* its
  Proposition omits `(0)` and `(z)`; these are included here.
* `SpectrumFormalization/Bezout.lean` — the **true fragment** of the Bézout
  theorem (`pointIdeal_not_le_of_no_common_zero`: `f, g` without a common zero at
  `a ∈ 𝔻` give `(f,g) ⊄ P_a`), together with a **counterexample**
  (`bezout_typeI_counterexample`) showing the paper's type-(i) claim is false:
  `f = g = 2` have empty (disjoint) zero sets, yet `(2) ⊆ (z, 2)`.

## Added in the cleanup and closure pass

All of the following build with no `sorry`/`admit`/`axiom`/`@[implemented_by]`/
`native_decide` and depend only on `propext`, `Classical.choice`, `Quot.sound`.

### Corrected Bézout theorem (`SpectrumFormalization/Bezout.lean`)

The paper's `thm:bezout` is false as printed; the repair is to add coprimality of
the constant terms, which is exactly what type-(i) containment obstructs.

* `dvd_ev0RR_of_mem_span_zp` — membership in `(z, p)` forces `p ∣ f(0)`.
* `bezout_not_le_typeI` — **step (i)**: if `gcd(f(0), g(0)) = 1` (formally
  `IsCoprime (ev0RR f) (ev0RR g)`), then `(f, g)` lies in no type-(i) maximal
  ideal. Proof: by `typeI_maximal_iff` such an ideal is `(z, p)`, forcing
  `p ∣ f(0)` and `p ∣ g(0)`, so `p` would be a unit of `ℤ`.
* `bezout_not_le_pointIdeal` — **step (ii)**: with disjoint zero sets, `(f, g)`
  lies in no point-evaluation ideal `P_a`, `a ∈ 𝔻`.
* `bezout_corrected` — **the conditional conclusion**, mirroring the paper's own
  structure: under the additional hypothesis `(H)` that every type-(iii) maximal
  ideal of `ℛ_ℝ` is a point-evaluation ideal `P_a`, disjoint zero sets plus
  coprime constant terms give `(f, g) = ℛ_ℝ`. Both extra hypotheses are explicit
  in the statement.
* `bezout_typeI_sharp` — **sharpness**: for every rational prime `p`, `f = g = p`
  have empty (hence disjoint) zero sets, yet `(p) ⊆ (z, p) ≠ ℛ_ℝ`. This
  generalizes `bezout_typeI_counterexample` (the case `p = 2`) and shows the
  coprimality hypothesis cannot be dropped.

### Type-(iii) maximal ideals (`SpectrumFormalization/TypeIII.lean`)

* `constTermImage` — the image `ev₀(M) ⊆ ℤ` of an ideal of `ℛ_ℝ`, as an ideal
  of `ℤ`.
* `span_zElt_ne_top` — `(z)` is a proper ideal.
* `typeIII_contains_one_add` — **`prop:interesting` (i)**: a type-(iii) maximal
  ideal `M` (`z ∉ M`, `M ∩ ℤ = 0`) contains an element of constant term `1`.
* `typeIII_contains_one`, `typeIII_isInP1` — the same conclusion without the
  redundant hypothesis, and the packaging `M ∈ 𝔓₁`.

*On the proof.* The printed `d > 1` argument (a field embedding into `ℤ/(d)`) is
shaky as written and is **replaced**. Writing `I = ev₀(M) = (d)`: if `1 ∉ I`,
choose a maximal ideal `Q ⊇ I` of `ℤ`. If `Q = (0)` then `M ≤ ker ev₀ = (z)`,
whence `M = (z) ∋ z` by maximality, contradicting `z ∉ M`; if `Q = (p)` then
`M ≤ ev₀⁻¹(p) = (z, p)`, whence `M = (z, p) ∋ z`, again a contradiction. The
argument in fact needs only `M` maximal and `z ∉ M`; the hypothesis `M ∩ ℤ = 0`
is retained in `typeIII_contains_one_add` for faithfulness to the paper's phrasing
and noted in the docstring as unnecessary (it follows from `trichotomy`).

### Classification of primes outside `𝔓₁`, converse direction (`SpectrumFormalization/PrimesOutside.lean`)

* `prime_contains_rat_prime` — a prime `P` containing a nonzero rational integer
  contains a rational prime (factor in `ℤ` and use `P.IsPrime.mem_or_mem`; the
  units `±1` cannot lie in `P`).
* `classify_prime_of_z_not_mem` — **the recorded gap is now closed**: a prime `P`
  with `z ∉ P` and `P ∩ ℤ ≠ 0` equals `(p)` for a rational prime `p`. The paper's
  `𝔽ₚ⟦z⟧`-image argument (which is not justified, since that image need not be a
  prime ideal) is **superseded** by this direct factorization argument.
* `spec_trichotomy` — the corrected trichotomy on `Spec(ℛ_ℝ)`: every prime `P`
  satisfies exactly one of (a) `z ∈ P`, and `P = (z)` or `(z, p)`; (b) `z ∉ P`,
  `P ∩ ℤ ≠ 0`, and `P = (p)`; (c) `z ∉ P` and `P ∩ ℤ = 0` (i.e. `P ∈ 𝔓₁`, which
  includes `(0)` and the point-evaluation ideals).

*Discrepancy recorded.* The converse holds with the hypothesis `P ∩ ℤ ≠ 0`, not
merely `P ≠ (0)`: any point-evaluation ideal `P_a` with `a ≠ 0` is a nonzero
prime with `z ∉ P_a` that is not of the form `(p)`. A claim about *all* primes
with `z ∉ P` and `P ≠ (0)` would therefore be false.

### Ultraproduct primes (`SpectrumFormalization/Ultraproduct.lean`)

The unconditional core of `prop:ultraproductprime` (i)–(ii), **without** Łoś's
theorem: Mathlib's `Filter.Germ` over an ultrafilter valued in a field is itself
a field.

For `Z ⊆ 𝔻` with `0 ∉ Z` and `𝒰 : Ultrafilter Z`:

* `evalOnSet`, `ultraHom` — evaluation along `Z`, and the induced ring
  homomorphism `Φ : ℛ_ℝ →+* Germ (𝒰 : Filter Z) ℂ`.
* `ultraPrime` — `P_𝒰 := ker Φ`; `ultraPrime_isPrime` — it is prime (kernel of a
  map into a field).
* `mem_ultraPrime` — membership criterion: `h ∈ P_𝒰 ↔ {a ∈ Z | h(a) = 0} ∈ 𝒰`.
* `zElt_not_mem_ultraPrime` — `z ∉ P_𝒰` (its germ is `a ↦ a`, whose zero set in
  `Z` is empty because `0 ∉ Z`, and `∅ ∉ 𝒰`).
* `intCast_mem_ultraPrime_iff` — `P_𝒰 ∩ ℤ = 0`.
* `ultraPrime_isTypeC` — hence `P_𝒰` is a prime of class (c) in
  `spec_trichotomy`.

The paper's nonemptiness hypothesis on `Z` is automatic here: an `Ultrafilter Z`
carries a `NeBot` witness.

### The ring-model bridge (`SpectrumFormalization/Bridge.lean`)

* `integer_realization_one` — the normalized form of Paper I's `thm:main`: a
  conjugation-invariant effective divisor `D` with `D.mult 0 = 0` is the zero
  divisor of a function holomorphic on `𝔻` with integer Taylor coefficients and
  value `1` at `0`. (Paper I's `integer_realization` discards the value at `0`
  when it multiplies in the monomial `z ^ D.mult 0`; the engine
  `integer_realization_of_data` supplies it.)
* `exists_RRsub_realization` — the same statement transported into the ring model:
  such a `D` is realized by an element `F ∈ ℛ_ℝ` with `ev₀ F = 1`.

This is the bridge that the remaining ultraproduct results would consume.

## Added in the sequel-completion pass (Tiers A–D)

### Order-of-vanishing plumbing (`SpectrumFormalization/OrderPlumbing.lean`)

The bridge speaks `IsZeroDivisorOf`, the unit-quotient lemma speaks `ODorder`;
both reduce to `analyticOrderNatAt` of a representative. This file connects them
and records the calculus of `ODorder` on `ℛ_ℝ`.

* `analyticOrderAt_ne_top_of_apply_ne_zero` — on the connected disk, a function
  analytic on `𝔻` and nonzero somewhere has finite analytic order everywhere in
  `𝔻` (identity theorem).
* `exists_RRsub_realization_order` (**A.1**) — divisor-level bridge: a
  conjugation-invariant `D` with `D.mult 0 = 0` is the order divisor of some
  `F ∈ ℛ_ℝ` with `ev₀ F = 1`.
* `ODorder_mul` (**A.2**) — additivity of `ODorder` on products, under the
  hypothesis `ev₀ x ≠ 0`, `ev₀ y ≠ 0` (the work order permits this weakening of
  "constant term `1`"; it is what rules out the locally-zero degenerate case).
* `ODevalAt_eq_zero_iff_ODorder_pos` (**A.3**) — value–order link, same
  hypothesis.
* `ODorder_zero_of_ev0RR_ne_zero`, `ODorder_zero_of_ev0RR_eq_one` (**A.4**).

### The partition property (`SpectrumFormalization/Partition.lean`)

* `partition_property` — **`prop:prime1ultrafilter`, divisor form.** For a prime
  `P` containing `f` with `ev₀ f = 1` and order divisor `D`, and a splitting
  `D = D₁ + D₂` into conjugation-invariant effective divisors, `P` contains an
  element of constant term `1` whose order divisor is `D₁` or `D₂`. Proof:
  realize `D₁`, `D₂` by A.1, multiply (A.2, A.4), apply `unit_quotient`, use
  primeness.

  *Recorded hypothesis.* Conjugation-invariance of the two pieces is essential
  and is not in the printed statement; this is the same omission already noted
  for `prop:ultraproductprime`.

### Ultraproduct trace and injectivity (`SpectrumFormalization/UltraTrace.lean`)

Standing data: `Z ⊆ 𝔻` with all points real, `0 ∉ Z`, `Z` discrete in `𝔻`, and
`𝒰 : Ultrafilter Z`. This is the manuscript's real-supported setting
(`|Z| ⊆ ℝ \ {0}`).

* `indicatorDivisor`, `indicatorDivisor_conjInvariant`,
  `indicatorDivisor_mult_zero` (**C.1**) — the indicator divisor of `W ⊆ Z`;
  conjugation-invariance comes exactly from realness of the points of `Z`.
* `exists_realizer` (**C.2**) — every `W ⊆ Z` is precisely the zero set in `𝔻` of
  an element of `ℛ_ℝ` of constant term `1`.
* `zeroSetIn`, `mem_ultraPrime_iff_zeroSet` (**C.3**) — the forward trace.
  *Discrepancy with the work order:* the hypothesis that the zero set of the
  element be contained in `Z` is **not needed**; the equivalence holds for every
  element of `ℛ_ℝ`, so the statement proved is stronger.
* `exists_generator_of_mem` (**C.4**) — the backward trace: every `S ∈ 𝒰` is the
  trace of the zero set of an element of `P_𝒰` of constant term `1`.
* `ultraPrime_isInP1` (**C.5**) — `P_𝒰 ∈ 𝔓₁`; together with the existing
  `ultraPrime_isTypeC` this closes `prop:ultraproductprime` (ii) in the
  real-supported form.
* `ultraPrime_injective` (**C.6**) — `𝒰 ↦ P_𝒰` is injective, i.e.
  `prop:ultraproductprime` (iv).

C.3 and C.4 together are the content of `prop:ultraproductprime` (iii)
(`𝓕_Z(P_𝒰) = 𝒰`) in the two directions actually used.

### `p`-adic evaluation primes (`SpectrumFormalization/PadicEval.lean`)

Formalization of `prop:padic` and `rem:padic` (new mathematics; all steps were
machine-checked, and no step of the printed sketch failed).

* `psEval` (**D.1**) — `p`-adic evaluation `ℤ⟦z⟧ →+* ℤ_[p]` at any `α ∈ ℤ_[p]`
  with `‖α‖ < 1` (the generality of `rem:padic`); convergence from
  `‖aₙαⁿ‖ ≤ ‖α‖ⁿ`, multiplicativity by the Cauchy product for absolutely
  convergent series in a complete normed ring. `psiP p` is the composite with the
  existing `coeffHom`, i.e. `ψ_p(f) = ∑ aₙ(-p)ⁿ`.
* `Qp`, `Qp_isPrime`, `zElt_add_p_mem`, `zElt_add_p_ne_zero`, `Qp_ne_bot`,
  `zElt_not_mem_Qp`, `intCast_mem_Qp_iff`, `psiP_mod_p`, `Qp_not_isInP1`
  (**D.2**) — the kernel `Q_p` is prime, nonzero (it contains `z + p`), contains
  neither `z` nor any nonzero integer, and lies outside `𝔓₁` because
  `ψ_p f ≡ a₀ (mod p)`.
* `primes_outside_classification_false` (**D.3**) — the packaged refutation: `Q_p`
  is a prime of class (c) different from `(0)`, `(z)`, `(q)`, `(z,q)` for every
  rational prime `q`. Hence class (c) of `spec_trichotomy` strictly contains
  `{⊥} ∪ 𝔓₁`, and the classification of the earlier version of the manuscript is
  false, as `rem:padic` states.
* `padicRem`, `padicDigit`, `padic_expansion`, `padic_tail_tendsto_zero`,
  `hasSum_padicDigits`, `psiP_surjective`, `padicInt_not_isField`, `quotQpEquiv`,
  `Qp_not_isMaximal` (**D.4**, the stretch goal) — the base-`(-p)` digit
  expansion, surjectivity of `ψ_p`, the isomorphism `ℛ_ℝ/Q_p ≅ ℤ_[p]`, and
  non-maximality of `Q_p`. This closes `prop:padic` (i) in full.

`SpectrumFormalization/AxiomCheck.lean` prints the axiom dependencies of all
Tier A–D headline declarations; each reports exactly `propext`,
`Classical.choice`, `Quot.sound`.

## Not yet formalized (and report items)

* **`prop:interesting` (iii)** and its dependents **`cor:Zinvariant`** and
  **`prop:prime1invariant`**: not formalized, and (iii) is **false as stated**.
  The printed proof extracts, from `d = 1`, a cofactor of constant term `±1` for
  every `z`-reduced element; this does not follow — `d = 1` supplies only *some*
  element of constant term `1`, not that every `z`-reduced element has one. (It
  also fails concretely for point-evaluation ideals.) The two completeness
  results lean on (iii), so they are left open. No correct weakening was found in
  the course of this pass.
* **`thm:bezout` as printed**: not formalized, because it is **false**; see
  `bezout_typeI_counterexample` and `bezout_typeI_sharp`. The corrected version
  `bezout_corrected` is formalized (above).
* **`prop:ultraproductprime` (ii)–(iv)** and **`prop:prime1ultrafilter`**: now
  **closed** in the real-supported form; see `UltraTrace.lean` and
  `Partition.lean` above. Two points remain on the record.
  1. Both results **require the realized sets to be conjugation-invariant**, a
     hypothesis the printed statements omit. `thm:main` realizes only
     conjugation-invariant divisors (a power series with real coefficients has a
     conjugation-invariant zero set), so the formalized versions carry either
     `|Z| ⊆ ℝ` (Tier C) or explicit conjugation-invariance of the two pieces
     (Tier B). For general complex `Z` the printed statements are not supported
     by the cited input.
  2. The forward trace `mem_ultraPrime_iff_zeroSet` needs no restriction on the
     zero set of the element; the extra hypothesis anticipated for it is
     unnecessary.
* **Łoś's theorem** in general form: not formalized, and not needed for the
  ultraproduct results above.
* The **converse direction of the classification of primes outside `𝔓₁`**, listed
  as open in the previous version of this file, is **now closed**; see
  `classify_prime_of_z_not_mem` and `spec_trichotomy` above.
* **Maximality of the ultraproduct primes `P_𝒰`**, **surjectivity of
  `𝒰 ↦ P_𝒰` onto `𝔓₁`**, and the **full ultrafilter property of `𝓕_Z(P)`**:
  open, and not attempted (report-only items). Nothing encountered in this pass
  bears on them either way.
* The **generation property** (`rem:nogeneration`) and the **completeness
  Conjecture for `𝒵`**: open, not attempted. No counterexample or proof idea was
  encountered.
* Whether **`Q_p = (z + p)`**: open. `z + p ∈ Q_p` is proved
  (`zElt_add_p_mem`); no containment in the other direction was attempted.
* The **classification of class (c)** in full: open. `Q_p` shows that class (c)
  strictly contains `{⊥} ∪ 𝔓₁`, as `rem:padic` claims.
