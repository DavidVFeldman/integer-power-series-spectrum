/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.GaussianRealization

/-!
# Factorization up to units in `𝒪(𝔻)` (Proposition `prop:associate`)

Formalizes the analytic content of Proposition `prop:associate` of Bannon–Feldman,
*Integer Coefficients Power Series with Prescribed Zero Sets*: **every function `f`
holomorphic on the open unit disk `𝔻` (and not identically zero) factors as
`f = g · u` on `𝔻`, where `g` is holomorphic on `𝔻` with all Taylor coefficients
Gaussian integers and `u` is holomorphic on `𝔻` and nowhere vanishing (a unit of
`𝒪(𝔻)`).**

The proof is exactly the paper's: the zero divisor `D` of `f` is realized by the
Gaussian-integer function `g` produced by `gaussian_realization` (Theorem
`prop:Zi`); then `u := f / g` has trivial divisor, hence extends to a nowhere-zero
holomorphic function, and `f = g · u` on all of `𝔻` by the identity principle.
-/

open Complex Filter Topology

namespace Weierstrass

/-- The open unit disk is preconnected (it is convex). -/
theorem isPreconnected_𝔻 : IsPreconnected (𝔻 : Set ℂ) :=
  (convex_ball (0 : ℂ) 1).isPreconnected

/-- For a function analytic on a neighborhood of `𝔻`, the value of its
Mathlib divisor at a point of `𝔻` is the natural analytic order there. -/
theorem divisor_eq_analyticOrderNat {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    {z : ℂ} (hz : z ∈ 𝔻) :
    (MeromorphicOn.divisor f 𝔻) z = (analyticOrderNatAt f z : ℤ) := by
  convert (hf.meromorphicOn.divisor_apply hz) using 1
  simp only [analyticOrderNatAt]
  rw [AnalyticAt.meromorphicOrderAt_eq (hf z hz)]
  cases analyticOrderAt f z <;> simp +decide

open Classical in
/-- The effective divisor of a nonzero holomorphic function: its multiplicity
function is the analytic order of vanishing inside `𝔻`. -/
noncomputable def analyticDivisor {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hne : ∃ z ∈ 𝔻, f z ≠ 0) : EffectiveDivisor where
  mult z := if z ∈ 𝔻 then analyticOrderNatAt f z else 0
  mult_eq_zero_of_not_mem_𝔻 := by intro z hz; rw [if_neg hz]
  finite_inter_compact := by
    intro K hK hK'
    have h_finite_zeros : Set.Finite {z ∈ K | f z = 0} := by
      have h_discrete : IsDiscrete {z ∈ Metric.ball 0 1 | f z = 0} := by
        have h_discrete : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (Metric.ball 0 1) := by
          convert AnalyticOnNhd.preimage_zero_mem_codiscreteWithin hf hne.choose_spec.2
            hne.choose_spec.1 _
          exact Metric.isConnected_ball (by norm_num)
        convert isDiscrete_of_codiscreteWithin h_discrete using 1
        exact Set.inter_comm _ _
      have h_compact : IsCompact {z ∈ K | f z = 0} := by
        have h_closed : IsClosed {z ∈ K | f z = 0} := by
          have h_cont : ContinuousOn f K := hf.continuousOn.mono hK
          exact h_cont.preimage_isClosed_of_isClosed hK'.isClosed isClosed_singleton
        exact hK'.of_isClosed_subset h_closed fun x hx => hx.1
      grind +suggestions
    refine h_finite_zeros.subset ?_
    intro z hz
    specialize hK hz.1
    simp_all +decide [analyticOrderNatAt]
    grind +suggestions

@[simp] theorem analyticDivisor_mult {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hne : ∃ z ∈ 𝔻, f z ≠ 0) {z : ℂ} (hz : z ∈ 𝔻) :
    (analyticDivisor hf hne).mult z = analyticOrderNatAt f z := by
  classical
  simp only [analyticDivisor, if_pos hz]

/-! ## Order bookkeeping -/

/--
An analytic function on `𝔻` that is not identically zero has finite
meromorphic order at every point of `𝔻`.
-/
theorem meromorphicOrderAt_ne_top_of_analytic {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hne : ∃ z ∈ 𝔻, f z ≠ 0) {z : ℂ} (hz : z ∈ 𝔻) :
    meromorphicOrderAt f z ≠ ⊤ := by
  by_contra h;
  -- By `AnalyticAt.meromorphicOrderAt_eq (hf z hz)`, `meromorphicOrderAt f z = ENat.map Nat.cast (analyticOrderAt f z)`. This is `⊤` iff `analyticOrderAt f z = ⊤`.
  have h_analyticOrderAt : analyticOrderAt f z = ⊤ := by
    rw [ AnalyticAt.meromorphicOrderAt_eq ( hf z hz ) ] at h;
    cases h' : analyticOrderAt f z <;> aesop;
  exact hne.elim fun x hx => hx.2 <| by have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf ( isPreconnected_𝔻 ) hz ( by simpa [ analyticOrderAt_eq_top ] using h_analyticOrderAt ) ; exact this ( show x ∈ Metric.ball 0 1 from hx.1 ) ;

/--
If `f` is analytic on `𝔻`, not identically zero, and vanishes at `z ∈ 𝔻`,
then its natural analytic order there is positive (in particular nonzero).
-/
theorem analyticOrderNatAt_ne_zero_of_eq_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hne : ∃ z ∈ 𝔻, f z ≠ 0) {z : ℂ} (hz : z ∈ 𝔻) (hfz : f z = 0) :
    analyticOrderNatAt f z ≠ 0 := by
  have h_analyticOrderAt_ne_zero : analyticOrderAt f z ≠ 0 := by
    exact fun h => hfz |> fun h' => by have := AnalyticAt.analyticOrderAt_eq_zero ( hf z hz ) ; aesop;
  contrapose! h_analyticOrderAt_ne_zero;
  cases h : analyticOrderAt f z <;> simp_all +decide [ analyticOrderNatAt ];
  obtain ⟨ w, hw₁, hw₂ ⟩ := hne;
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf ( isPreconnected_𝔻 ) ( show z ∈ Metric.ball 0 1 from by simpa using hz ) ( by simpa [ analyticOrderAt_eq_top ] using h ) ; exact hw₂ <| this ( show w ∈ Metric.ball 0 1 from by simpa using hw₁ ) ;

/--
A function vanishing on all of `𝔻` has zero natural analytic order at each
point of `𝔻` (its analytic order is `⊤`, whose `toNat` is `0`).
-/
theorem analyticOrderNatAt_eq_zero_of_forall_eq_zero {g : ℂ → ℂ}
    (hg0 : ∀ z ∈ 𝔻, g z = 0) {z : ℂ} (hz : z ∈ 𝔻) :
    analyticOrderNatAt g z = 0 := by
  rw [ analyticOrderNatAt, analyticOrderAt ];
  split_ifs <;> simp_all +decide [ Metric.mem_ball ];
  exact False.elim <| ‹¬∀ᶠ z in nhds z, g z = 0› <| Filter.eventually_of_mem ( IsOpen.mem_nhds ( isOpen_lt continuous_norm continuous_const ) hz ) hg0

/--
The Taylor coefficients of the constant function `1` are Gaussian integers.
-/
theorem taylorCoeff_one_gaussian (m : ℕ) :
    ∃ w : GaussianInt, taylorCoeff (fun _ : ℂ => (1 : ℂ)) m = w := by
  rcases m with ( _ | m ) <;> simp_all +decide [ taylorCoeff ];
  · exact ⟨ 1, by norm_num [ GaussianInt.toComplex_def ] ⟩;
  · rw [ iteratedDeriv_succ' ];
    exact ⟨ 0, by simp +decide ⟩

/-! ## The core divisor computation and quotient -/

/--
If `f, g` are analytic on `𝔻`, both not identically zero, and have equal
natural analytic orders throughout `𝔻`, then the divisor of the quotient `f / g`
is zero.
-/
theorem divisor_mul_inv_eq_zero {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hg : AnalyticOnNhd ℂ g 𝔻) (hfne : ∃ z ∈ 𝔻, f z ≠ 0) (hgne : ∃ z ∈ 𝔻, g z ≠ 0)
    (horder : ∀ z ∈ 𝔻, analyticOrderNatAt f z = analyticOrderNatAt g z) :
    MeromorphicOn.divisor (f * g⁻¹) 𝔻 = 0 := by
  convert ( MeromorphicOn.divisor_mul ( hf.meromorphicOn ) ( hg.meromorphicOn.inv ) _ _ ) using 1;
  · ext z; by_cases hz : z ∈ Metric.ball 0 1 <;> simp_all +decide ;
    rw [ divisor_eq_analyticOrderNat hf ( by simpa using hz ), divisor_eq_analyticOrderNat hg ( by simpa using hz ) ] ; aesop;
  · exact fun z a => meromorphicOrderAt_ne_top_of_analytic hf hfne a;
  · intro z hz;
    rw [ meromorphicOrderAt_inv ];
    exact fun h => by have := meromorphicOrderAt_ne_top_of_analytic hg hgne hz; aesop;

/-- The codiscrete-within filter on the open unit disk is nontrivial (`𝔻` is a
nonempty perfect set), so a statement holding on a codiscrete subset of `𝔻` cannot
be vacuous. -/
theorem codiscreteWithin_𝔻_neBot : (codiscreteWithin (𝔻 : Set ℂ)).NeBot := by
  rw [Filter.neBot_iff, Ne, ← Filter.empty_mem_iff_bot,
    codiscreteWithin_iff_locallyEmptyComplementWithin]
  push_neg
  refine ⟨0, by simp, ?_⟩
  intro t ht
  rw [Set.diff_empty]
  have hb : (𝔻 : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (by norm_num))
  exact Filter.nonempty_of_mem (Filter.inter_mem ht hb)

/-- If `f, g` are analytic on `𝔻`, `g` is not identically zero, and the divisor of
`f / g` is zero, then `f = g · u` on `𝔻` for a nowhere-vanishing holomorphic `u`. -/
theorem factor_of_divisor_zero {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hg : AnalyticOnNhd ℂ g 𝔻) (hgne : ∃ z ∈ 𝔻, g z ≠ 0)
    (hfne : ∃ z ∈ 𝔻, f z ≠ 0)
    (hdiv : MeromorphicOn.divisor (f * g⁻¹) 𝔻 = 0) :
    ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u 𝔻 ∧ (∀ z ∈ 𝔻, u z ≠ 0) ∧
      Set.EqOn f (fun z => g z * u z) 𝔻 := by
  obtain ⟨u, hu_an, hu_ne, hu_eq⟩ :=
    MeromorphicOn.extract_zeros_poles (hf.meromorphicOn.mul hg.meromorphicOn.inv)
      (by
        rintro ⟨w, hw⟩
        rw [meromorphicOrderAt_mul (hf w hw).meromorphicAt (hg w hw).meromorphicAt.inv,
          meromorphicOrderAt_inv]
        have h1 := meromorphicOrderAt_ne_top_of_analytic hf hfne hw
        have h2 := meromorphicOrderAt_ne_top_of_analytic hg hgne hw
        lift meromorphicOrderAt f w to ℤ using h1 with a
        lift meromorphicOrderAt g w to ℤ using h2 with b
        simp)
      (by rw [hdiv]; simp [Function.locallyFinsuppWithin.support])
  -- Since the divisor is zero, the extracted factorization simplifies to `f/g = u`.
  have key : f * g⁻¹ =ᶠ[codiscreteWithin (𝔻 : Set ℂ)] u := by
    have h := hu_eq
    rw [hdiv] at h
    simpa using h
  -- The zeros of `g` are codiscrete in `𝔻`.
  have hgc : ∀ᶠ z in codiscreteWithin (𝔻 : Set ℂ), g z ≠ 0 := by
    have := AnalyticOnNhd.preimage_zero_mem_codiscreteWithin hg hgne.choose_spec.2
      hgne.choose_spec.1 (Metric.isConnected_ball (by norm_num))
    filter_upwards [this] with z hz using hz
  -- Hence `f = g · u` on a codiscrete subset of `𝔻`.
  have hfeq : f =ᶠ[codiscreteWithin (𝔻 : Set ℂ)] fun z => g z * u z := by
    filter_upwards [key, hgc] with z hz1 hz2
    have hz1' : f z * (g z)⁻¹ = u z := hz1
    rw [← hz1']; field_simp
  refine ⟨u, hu_an, fun z hz => hu_ne ⟨z, hz⟩, ?_⟩
  rcases hf.eqOn_or_eventually_ne_of_preconnected (hg.mul hu_an) isPreconnected_𝔻 with h | h
  · exact h
  · have hbot : codiscreteWithin (𝔻 : Set ℂ) = ⊥ := by
      rw [← Filter.eventually_false_iff_eq_bot]
      filter_upwards [hfeq, h] with z h1 h2 using h2 h1
    exact absurd hbot codiscreteWithin_𝔻_neBot.ne

/-! ## Main result -/

/-- **Proposition `prop:associate`.** Every function holomorphic on `𝔻` that is
not identically zero factors on `𝔻` as `g · u` with `g` holomorphic on `𝔻` having
Gaussian-integer Taylor coefficients and `u` holomorphic on `𝔻` and nowhere
vanishing. -/
theorem associate_factorization {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    (hne : ∃ z ∈ 𝔻, f z ≠ 0) :
    ∃ g u : ℂ → ℂ, AnalyticOnNhd ℂ g 𝔻 ∧
      (∀ m : ℕ, ∃ w : GaussianInt, taylorCoeff g m = w) ∧
      AnalyticOnNhd ℂ u 𝔻 ∧ (∀ z ∈ 𝔻, u z ≠ 0) ∧
      Set.EqOn f (fun z => g z * u z) 𝔻 := by
  obtain ⟨g, hg_holo, hg_gauss, hg_zero⟩ := gaussian_realization (analyticDivisor hf hne)
  have horder : ∀ z ∈ 𝔻, analyticOrderNatAt f z = analyticOrderNatAt g z := by
    intro z hz
    have h := hg_zero z hz
    rwa [analyticDivisor_mult hf hne hz] at h
  by_cases hgne : ∃ z ∈ 𝔻, g z ≠ 0
  · obtain ⟨u, hu1, hu2, hu3⟩ :=
      factor_of_divisor_zero hf hg_holo hgne hne
        (divisor_mul_inv_eq_zero hf hg_holo hne hgne horder)
    exact ⟨g, u, hg_holo, hg_gauss, hu1, hu2, hu3⟩
  · -- degenerate case: `g` is identically zero on `𝔻`, so `f` is nowhere zero;
    -- take `g := 1` and `u := f`.
    push_neg at hgne
    have hfnz : ∀ z ∈ 𝔻, f z ≠ 0 := by
      intro z hz hfz
      have hgz : analyticOrderNatAt g z = 0 :=
        analyticOrderNatAt_eq_zero_of_forall_eq_zero hgne hz
      have hfz0 : analyticOrderNatAt f z = 0 := by rw [horder z hz, hgz]
      exact analyticOrderNatAt_ne_zero_of_eq_zero hf hne hz hfz hfz0
    refine ⟨(fun _ => 1), f, analyticOnNhd_const, taylorCoeff_one_gaussian, hf, hfnz, ?_⟩
    intro z _
    simp

end Weierstrass