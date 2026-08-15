# Formalization status

This documents the correspondence between the paper *Integer Coefficients Power
Series with Prescribed Zero Sets* (Bannon–Feldman) and the Lean development in
`RequestProject/`. Every listed declaration builds with no `sorry` and depends
only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

## Section 2 — Modified Elementary Factors (complete)

`RequestProject/Main.lean`:
- `H`, `E`, `Gtail`, `G` — the modified elementary factor and its exponent.
- `E_at_zero` — Lemma "Structure", part (i): `E n c 0 = 1`.
- `E_eq_exp_G` — eq. (Eexp)–(Gdef): `E n c w = exp (G n c w)` on `‖w‖ < 1`.
- `E_ne_zero_of_norm_lt_one` — part (iv): nonvanishing on the unit disk.
- `E_differentiable` — part (v): `E n c` is entire.
- `E_eq_zero_iff` — part (v): the only zero (over `ℂ`) is the simple zero `w = 1`.
- `E_expansion` — parts (ii)–(iii): `E n c w = 1 + w^(n+1) Φ w` with `Φ 0 = (c-1)/(n+1)`.

`RequestProject/AffineControl.lean` — Lemma "Affine coefficient control":
- `taylorCoeff` and its calculus (`taylorCoeff_congr`, `taylorCoeff_add`,
  `taylorCoeff_pow_mul_lt`, `taylorCoeff_pow_mul_eq`).
- `affine_remainder` — remainder form `h·E n c (z/a) = h + z^(n+1) R`.
- `affine_coeff_low` — part (i): coefficients of degree `≤ n` are unchanged.
- `affine_coeff_top` — part (ii): degree `n+1` shifts by `(c-1)/((n+1)a^(n+1))`.

## Main theorem — necessity and the conjugate-pairing device

`RequestProject/Main.lean`:
- `zeroSet_conj_invariant` — necessity: a function with real Taylor coefficients
  has a conjugation-invariant zero set.

`RequestProject/RealCoeffs.lean`:
- `E_conj` — `conj (E n c w) = E n (conj c) (conj w)`.
- `deriv_conj_comp`, `differentiable_conj_comp`, `iteratedDeriv_conj_comp` —
  calculus of `conj ∘ F ∘ conj`.
- `taylorCoeff_isReal_of_conjSymm` — conjugation symmetry forces real coefficients.
- `pair_conjSymm`, `pair_taylorCoeff_isReal` — the conjugate-pair product
  `E n c (z/a)·E n (conj c)(z/conj a)` has real Taylor coefficients (the device
  keeping partial-product coefficients real in the proof of Theorem (main)).

## Section 3 — Proofs (key ingredients)

`RequestProject/Convergence.lean` — the Step 3 estimates:
- `Gtail_summable`, `Gtail_norm_le` — convergence and bound for the tail series.
- `G_norm_le` — `‖G n c w‖ ≤ ‖c-1‖/(n+1)·ρ^(n+1) + ρ^(n+2)/(1-ρ)` on `‖w‖ ≤ ρ < 1`.
- `E_sub_one_norm_le` — `‖E n c w - 1‖ ≤ 2‖G n c w‖`, feeding the product criterion.

`RequestProject/Gates.lean` — Step 3 (Convergence), the analytic core of the
Section 3 construction: infinite-product convergence to a holomorphic limit.
- `tprod_holo_of_forall_compact` — general principle: if each factor `F n` is
  entire and on every compact subset of `𝔻 = ball 0 1` the differences
  `‖F n - 1‖` are eventually dominated (uniformly) by a summable sequence, then
  the partial products `∏_{n<N} F n` converge locally uniformly on `𝔻` to
  `z ↦ ∏' n, F n z`, which is holomorphic on `𝔻`.
- `E_factor_bound` — the Step 3 quantitative estimate: under the rounding bound
  (cnbound) and `|a_n| → 1`, on each closed subdisk `‖z‖ ≤ r < s < 1` the factor
  differences `‖E_n(z/a_{n+1};c_{n+1}) - 1‖` are eventually dominated by the
  summable sequence `2·((√2/2) r^(n+1) + (r/s)^(n+2)/(1 - r/s))`.
- `gates_convergence` — the conclusion: the partial products
  `∏_{n<N} E_n(z/a_{n+1};c_{n+1})` converge locally uniformly on `𝔻` to
  `z ↦ ∏' n, E_n(z/a_{n+1};c_{n+1})`, and the limit is holomorphic on `𝔻`.

`RequestProject/Freezing.lean` — Step 4 (Freezing of coefficients in the limit):
having the holomorphic limit `f(z) = ∏' n, E_n(z/α n;γ n)` from `Gates.lean`, each
Taylor coefficient of `f` is frozen at its finite stage.
- `iteratedDeriv_differentiableOn` — iterated derivatives of a function holomorphic
  on an open set are holomorphic there.
- `iteratedDeriv_tendstoLocallyUniformlyOn` — local uniform convergence transfers to
  all iterated derivatives (iterating `TendstoLocallyUniformlyOn.deriv`).
- `taylorCoeff_tendsto_of_tendstoLocallyUniformlyOn` — Taylor coefficients are
  continuous under local uniform convergence of holomorphic functions.
- `partialProd_taylorCoeff_step` — one stabilization step: multiplying by `E_N`
  leaves every coefficient of degree `≤ N` unchanged (`[z^m]P_{N+1} = [z^m]P_N`
  for `m ≤ N`), via `affine_coeff_low`.
- `partialProd_taylorCoeff_stable` — coefficients stabilize from stage `m` on:
  `[z^m]P_N = [z^m]P_m` for all `N ≥ m`.
- `gates_coeff_freeze` — the conclusion: `[z^m] (∏' n, E_n(z/α n;γ n)) = [z^m] P_N`
  for every `N ≥ m`; the coefficients of the limit are exactly the frozen
  coefficients of the finite stages.

`RequestProject/Rounding.lean` — the Step 1 rounding device:
- `exists_gaussian_int_near` — every `v ∈ ℂ` is within `√2/2` of a Gaussian integer.
- `exists_param_round` — choosing the parameter `c` to round the degree-`(n+1)`
  coefficient of `h·E n c (z/a)` to a Gaussian integer, with `‖c-1‖ ≤
  (√2/2)(n+1)|a|^(n+1)` (the bound (cnbound)).

## Section 4 — A Worked Example (complete)

`RequestProject/WorkedExample.lean` (with `a₁ = 1/3 + i/4`):
- `E0_coeff_one` — `[z^1] E₀(z/a; 1) = 0`.
- `E0_coeff_two` — `[z^2] E₀(z/a; 1) = -1/(2a²)`.
- `E0_coeff_two_at_a1` — `[z^2] E₀(z/a₁; 1) = (-504 + 1728 i)/625`.
- `a1_rounding_error` — rounding error to `-1 + 3i` is `√58/25`.
- `a1_rounding_error_le` — `√58/25 ≤ √2/2`.

## Section 5 — Ring-theoretic consequences

### Abstract layer (`RequestProject/RingConsequences.lean`)

`RequestProject/RingConsequences.lean` — the implicit implications of the Section 5
paragraph "The key algebraic consequence of Theorem `prop:Zi` … Corollary
`cor:ideals` and Proposition `prop:inject` flow directly from this." These are
pure ring theory once the factorization statement of Proposition `prop:associate`
is available, so they are proved for an abstract commutative ring `O` with a
subring `R` (modelling `𝒪(𝔻)` and `ℛ`) under the factorization property taken as
an explicit hypothesis. When the realization theorem `prop:Zi` (hence
`prop:associate`) is confirmed for the concrete rings, these become available by
instantiation.
- `HasSubringFactorization` — the hypothesis: every `f ∈ O` equals `g · u` with
  `g ∈ R` and `u ∈ Oˣ` (Proposition `prop:associate`).
- `ideal_eq_map_comap` — Corollary `cor:ideals`: every ideal `I` satisfies
  `I = (I ∩ R)·O`.
- `comap_subtype_injective` — the contraction `I ↦ I ∩ R` is injective on *all*
  ideals (stronger than the paper's maximal-ideal statement, whose proof invokes
  maximality).
- `contraction_maximalSpec_injective` — Proposition `prop:inject`: the paper's
  contraction map `φ : MaxSpec(𝒪(𝔻)) → Spec(ℛ)` is injective.
- `contract_ne_bot` — well-definedness: the contraction of a nonzero ideal is
  nonzero.

### Concrete rings and unconditional consequences (`RequestProject/DiskRing.lean`, `ConcreteUnits.lean`, `ConcreteFiber.lean`)

The concrete rings are now built and the abstract results instantiated, making
Corollary `cor:ideals` and Proposition `prop:inject` **unconditional**. All
declarations build with no `sorry` and depend only on `propext`,
`Classical.choice`, `Quot.sound`.

`RequestProject/DiskRing.lean` — the concrete rings `𝒪(𝔻)` and `ℛ`:
- `diskAnalytic` — the subring of `ℂ → ℂ` of functions analytic on `𝔻`.
- `vanishIdeal` — the ideal of functions vanishing on `𝔻`.
- `OD := diskAnalytic ⧸ vanishIdeal` — `𝒪(𝔻)`, holomorphic functions on `𝔻`
  identified when they agree on `𝔻` (`ODmk_eq_iff`). Units of `OD` are exactly the
  classes of nowhere-vanishing holomorphic functions (`isUnit_ODmk_of_nonvanishing`).
- `taylorCoeff_mul_eq` — the Cauchy product for Taylor coefficients (via the
  Leibniz rule `iteratedDeriv_mul`), giving that Gaussian-integer coefficients are
  preserved under multiplication (`IsGaussianCoeffs.mul`).
- `Rpre` / `Rsub` — `ℛ = ℤ[i][[z]] ∩ 𝒪(𝔻)`, the subring of `OD` of classes with
  Gaussian-integer Taylor coefficients.
- `hasSubringFactorization` — Proposition `prop:associate` for the concrete rings
  (`HasSubringFactorization Rsub`), obtained from `associate_factorization`.
- `ideal_eq_map_comap_OD` — **Corollary `cor:ideals`, unconditional**:
  `I = (I ∩ ℛ)·𝒪(𝔻)` for every ideal `I` of `𝒪(𝔻)`.
- `contraction_maximalSpec_injective_OD` — **Proposition `prop:inject`,
  unconditional**: the contraction map `φ : MaxSpec(𝒪(𝔻)) → Spec(ℛ)` is injective.

`RequestProject/ConcreteUnits.lean` — **Proposition `prop:units`** (`units_Rsub`):
an element of `ℛ` is a unit iff it is a unit of `𝒪(𝔻)` (nowhere vanishing on `𝔻`)
and its value at `0` is a unit of `ℤ[i]`. The core input is
`isGaussianCoeffs_inv`: the reciprocal of a nowhere-vanishing function with
Gaussian coefficients and Gaussian-unit constant term again has Gaussian
coefficients (proved by the triangular convolution recurrence via
`taylorCoeff_mul_eq`).

`RequestProject/ConcreteFiber.lean` — **Proposition `prop:fiber` (core)**:
evaluation at `0` is a surjective ring homomorphism `ev0R : ℛ → ℤ[i]`
(`ev0R_surjective`) whose kernel is the augmentation ideal
`𝔫₀ = {g ∈ ℛ : g(0) = 0}` (`augIdeal`, `mem_augIdeal`), yielding the isomorphism
`ℛ / 𝔫₀ ≅ ℤ[i]` (`fiberEquiv`).

`RequestProject/FiberPrimes.lean` — **Proposition `prop:fiber` (remainder)**,
which completes Paper I:
- `fiberPrimesEquiv` — the **quotient correspondence**: an *order isomorphism*
  `{P : Ideal ℛ // P.IsPrime ∧ 𝔫₀ ≤ P} ≃o {Q : Ideal ℤ[i] // Q.IsPrime}`, with
  forward map `P ↦ P.map ev0R` and inverse `Q ↦ Q.comap ev0R`, obtained from the
  ideal correspondence along the surjection `ev0R` with kernel `𝔫₀`.
- `m0`, `m0_isMaximal` — the evaluation ideal `𝔪₀ = ker(ev₀ : 𝒪(𝔻) → ℂ)` is
  maximal (evaluation at `0` is surjective onto `ℂ` via constants).
- `zR`, `exists_zOD_factor` — the coordinate function `z` inside `ℛ`, and
  division by `z` in `𝒪(𝔻)` (via `dslope`): a holomorphic function vanishing at
  `0` is `z` times a holomorphic function.
- `augIdeal_map_eq_m0` — **`𝔫₀·𝒪(𝔻) = 𝔪₀`**.
- `comap_m0` — `𝔪₀ ∩ ℛ = 𝔫₀`.
- `phi_fiber` — **only `𝔫₀` lies in the image of `φ`**: a maximal ideal `𝔪` of
  `𝒪(𝔻)` whose contraction contains `𝔫₀` equals `𝔪₀`, and its contraction is
  exactly `𝔫₀`. Restated as `not_comap_of_augIdeal_lt`: no prime of `ℛ` strictly
  containing `𝔫₀` is a contraction of a maximal ideal of `𝒪(𝔻)`.

## Section 3 — Gaussian-integer realization (`WeierstrassFormalization` library)

A second, self-contained development lives in the `WeierstrassFormalization/`
library. It carries the Section 3 construction all the way to the realization
theorem `prop:Zi`. Every declaration builds with no `sorry` and depends only on
the standard axioms `propext`, `Classical.choice`, `Quot.sound`.

- `WeierstrassFormalization/Basic.lean` — the open unit disk `𝔻` (`mem_𝔻_iff`),
  `HolomorphicOn`, and `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`.
- `WeierstrassFormalization/ElementaryFactor.lean` — the modified elementary
  factor `E`, exponent `G`, and coefficient operator `taylorCoeff f m`, with
  `E_zero`, `E_zero_iff`, `E_eq_exp_G`, `E_expansion`, the `taylorCoeff` calculus,
  and `taylorCoeff_E_eq_zero`, `taylorCoeff_E_succ`.
- `WeierstrassFormalization/Divisor.lean` — `EffectiveDivisor` on `𝔻`,
  `ConjInvariant`, and `IsZeroDivisorOf`.
- `WeierstrassFormalization/AffineControl.lean` — affine coefficient control
  (`taylorCoeff_mul_E_eq_of_le`, `taylorCoeff_mul_E_succ`,
  `exists_c_taylorCoeff_mul_E_succ_eq`).
- `WeierstrassFormalization/WeierstrassProduct.lean` — the full scaffolding:
  Gaussian-integer rounding (`nearestGaussianInt`, `norm_sub_nearestGaussianInt_le`),
  the exponent bound `norm_G_le`, the divisor enumeration
  `exists_enum_of_effectiveDivisor`, the inductive coefficient forcing
  `exists_coeffSeq`, the Weierstrass `M`-test `exists_Mtest_of_coeffSeq`,
  local-uniform convergence and holomorphy of the product
  (`hasProdLocallyUniformlyOn_factors`, `holomorphicOn_tprod_factors`), the
  zero-divisor identification `isZeroDivisorOf_tprod_factors`, and the coefficient
  stabilization `taylorCoeff_tprod_factors_eq_partial`.
- `WeierstrassFormalization/GaussianRealization.lean` — **Theorem `prop:Zi`**
  (`gaussian_realization`): every effective divisor `D` on `𝔻` is the zero divisor
  of a function `f` holomorphic on `𝔻` all of whose Taylor coefficients are
  Gaussian integers. The proof assembles the enumeration, forcing, `M`-test,
  convergence, and order computations above, with the zero at the origin supplied
  by an explicit monomial factor `z ^ D.mult 0`. Supporting lemmas:
  `partialProduct_taylorCoeff_stable`, `tprod_taylorCoeff_gaussian`,
  `taylorCoeff_monomial_mul`, `analyticOrderNatAt_monomial_mul_of_ne`,
  `analyticOrderNatAt_monomial_mul_at_zero`.
- `WeierstrassFormalization/AssociateFactorization.lean` — **Proposition
  `prop:associate`** at the level of holomorphic functions
  (`associate_factorization`): every function `f` holomorphic on `𝔻` and not
  identically zero factors on `𝔻` as `f = g · u`, where `g` is holomorphic on `𝔻`
  with all Taylor coefficients Gaussian integers and `u` is holomorphic on `𝔻` and
  nowhere vanishing (a unit of `𝒪(𝔻)`). The proof realizes the zero divisor of `f`
  by `gaussian_realization` (Theorem `prop:Zi`), shows the quotient `f / g` has
  trivial divisor, hence extends to a nowhere-zero holomorphic function via
  `MeromorphicOn.extract_zeros_poles`, and upgrades the resulting codiscrete
  equality to equality on all of `𝔻` by the identity principle. Supporting lemmas:
  `isPreconnected_𝔻`, `divisor_eq_analyticOrderNat`, `analyticDivisor`,
  `meromorphicOrderAt_ne_top_of_analytic`, `analyticOrderNatAt_ne_zero_of_eq_zero`,
  `analyticOrderNatAt_eq_zero_of_forall_eq_zero`, `taylorCoeff_one_gaussian`,
  `divisor_mul_inv_eq_zero`, `codiscreteWithin_𝔻_neBot`, `factor_of_divisor_zero`.

This is exactly the factorization property that the Section 5 corollary
`cor:ideals` (Corollary on ideals) and `prop:inject` rely on: the abstract,
ring-theoretic consequences in `RequestProject/RingConsequences.lean` are proved
from the hypothesis `HasSubringFactorization`, and `associate_factorization`
establishes that hypothesis analytically for holomorphic functions on `𝔻`.

## Theorem `thm:main` (sufficiency) and Proposition `prop:nv` (`WeierstrassFormalization` library)

Both previously-open analytic constructions are now formalized. Every declaration
builds with no `sorry` and depends only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound`.

- `WeierstrassFormalization/NowhereVanishing.lean` — **Proposition `prop:nv`**
  (`nowhere_vanishing_realization`): for `a : ℕ → ℂ` with `‖a n‖ > 1` and
  `‖a n‖ → 1`, there is `f` holomorphic on `𝔻` with Gaussian-integer Taylor
  coefficients, nowhere vanishing on `𝔻`, with `f 0 = 1`. It reuses the Section 3
  product machinery (`exists_coeffSeq`, `exists_Mtest_of_coeffSeq`,
  `holomorphicOn_tprod_factors`, `isZeroDivisorOf_tprod_factors`): the escape
  hypothesis is automatic because all zeros lie outside `𝔻`, and nonvanishing
  follows since every factor is nonzero on `𝔻`. (The `‖a n‖ → 1` hypothesis is the
  paper's; the construction in fact only needs `‖a n‖ > 1`.)

- `WeierstrassFormalization/IntegerRealization.lean` — **Theorem `thm:main`
  (sufficiency)** (`integer_realization`): a conjugation-invariant effective
  divisor `D` on `𝔻` is the zero divisor of a holomorphic function on `𝔻` with all
  Taylor coefficients in `ℤ`. Organized as: `exists_Mtest_general` (the Weierstrass
  `M`-test for a general order function `n : ℕ → ℕ`, generalizing
  `exists_Mtest_of_coeffSeq`); `integer_realization_of_data` (the engine: from data
  `(n, a, c)` with the `M`-test bound, order-growth, and integrality of the
  partial-product coefficients, the product `∏' k, Eₖ` is holomorphic, has integer
  coefficients, the prescribed zero counts, and value `1` at `0`);
  `exists_integer_data` (assembling the paired enumeration and the rounding); and
  `integer_realization` (with the origin zero supplied by a monomial `z ^ D.mult 0`).
  The generalized coefficient-freezing lemma
  `taylorCoeff_tprod_factors_eq_partial` (in `WeierstrassProduct.lean`) was weakened
  from `StrictMono n` to a tail condition to support the paired order function, and
  `exists_enum_of_effectiveDivisor` was extended to expose that its values lie in
  the support (or are the pad `2`).

- `WeierstrassFormalization/PairedRounding.lean` — the **rounding engine**. From an
  enumeration `(n, a)` organized into slots (level sets of `n` of size ≤ 2, with
  conjugate pairs sharing a slot: `PairedEnum`), the correction parameters
  `paramSeq n a` are built by an inductive rounding recursion (`auxState`,
  `roundStep`). Using the conjugation involution `sigmaIdx`, every partial product
  over a `σ`-closed prefix is shown conjugation-symmetric (`sigmaIdx_param`,
  `PPfun_conjSymm`), hence real-coefficiented at slot boundaries, so the rounding
  lands in `ℤ`. `exists_rounding` packages the rounding bound (`paramSeq_bound`) and
  the integrality of the completed-slot coefficients (`paramSeq_coeff_int`, via the
  slot-completion lemmas `coeff_leader_lone`, `coeff_leader_pair`).

- `WeierstrassFormalization/PairedEnumeration.lean` — the **paired enumeration**
  (`exists_pairedEnum`). The strictly-upper-half-plane part and the real part of `D`
  are enumerated separately (`exists_enum_upper`, `exists_enum_real`), then
  interleaved four-per-period into the flat sequence `pairA` with order
  `pairN k = k / 2`: even slots carry a conjugate pair `(u t, conj (u t))`, odd
  slots a pair of real points `(r (2t), r (2t+1))`. `pairedEnum_pairA`,
  `hesc_pairA`, and `count_pairA` establish the `PairedEnum` conditions, the escape
  property, and the zero counts (`D.mult z = {k | pairA u r k = z}.ncard` for
  `z ∈ 𝔻`).

## Not yet formalized

*(Empty.)* Paper I is fully formalized. Section 5 is complete and unconditional:
Corollary `cor:ideals`, Propositions `prop:inject`, `prop:units`, and
`prop:fiber` in full — the core isomorphism `ℛ/𝔫₀ ≅ ℤ[i]` (`fiberEquiv`), the
quotient correspondence with `Spec(ℤ[i])` (`fiberPrimesEquiv`), and the
description of the image of `φ` (`phi_fiber`).

*Auxiliary relocation.* `taylorCoeff_id` (the Taylor coefficients of `z ↦ z`)
moved from `SpectrumFormalization/Shift.lean` to `RequestProject/DiskRing.lean`
so that both libraries can use it; the statement is unchanged.
