import SpectrumFormalization.Shift

/-!
# `𝒪(𝔻)` and `ℛ_ℝ` are integral domains, and `ℛ_ℝ/(z) ≅ ℤ`

The ring `𝒪(𝔻)` of holomorphic functions on the connected open disk is an
integral domain (identity theorem). Consequently the subring `ℛ_ℝ` is a domain,
so the zero ideal `(0)` is prime. We also identify the kernel of the
constant-term homomorphism `ev₀ : ℛ_ℝ → ℤ` as the principal ideal `(z)`
(division by `z`), so `ℛ_ℝ/(z) ≅ ℤ`.
-/

open Complex Weierstrass

namespace RequestProject

/-! ## `𝒪(𝔻)` is an integral domain -/

/-
`𝒪(𝔻)` is nontrivial: the constant function `1` does not vanish on `𝔻`.
-/
instance OD_nontrivial : Nontrivial OD := by
  refine' ⟨ _, _, _ ⟩;
  exact ODmk ⟨ 1, analyticOnNhd_const ⟩;
  exact ODmk ⟨ 0, analyticOnNhd_const ⟩;
  intro h; have := ODmk_eq_iff.mp h; have := this 0 ( Metric.mem_ball_self zero_lt_one ) ; norm_num at this;

/-
**Identity theorem consequence.** `𝒪(𝔻)` has no zero divisors: if the
product of two holomorphic functions vanishes identically on the connected disk
`𝔻`, then one of the factors vanishes identically on `𝔻`.
-/
instance OD_noZeroDivisors : NoZeroDivisors OD := by
  constructor
  generalize_proofs at *;
  intro a b hab
  obtain ⟨f, hf⟩ : ∃ f : diskAnalytic, a = ODmk f := by
    exact ⟨ _, Eq.symm <| Ideal.Quotient.mk_surjective a |> Classical.choose_spec ⟩
  obtain ⟨g, hg⟩ : ∃ g : diskAnalytic, b = ODmk g := by
    exact ⟨ _, Eq.symm <| Ideal.Quotient.mk_out _ ⟩
  have hfg : f * g ∈ vanishIdeal := by
    convert Ideal.Quotient.eq_zero_iff_mem.mp ( show ODmk ( f * g ) = 0 from ?_ ) using 1
    generalize_proofs at *;
    convert hab using 1 ; rw [ hf, hg ] ; rfl
  have hfg_zero : ∀ z ∈ 𝔻, (f : ℂ → ℂ) z * (g : ℂ → ℂ) z = 0 := by
    exact fun z hz => mem_vanishIdeal.mp hfg z hz
  have hfg_zero_or : (∀ z ∈ 𝔻, (f : ℂ → ℂ) z = 0) ∨ (∀ z ∈ 𝔻, (g : ℂ → ℂ) z = 0) := by
    by_cases hf_zero : ∃ z ∈ Metric.ball 0 1, (f : ℂ → ℂ) z ≠ 0;
    · obtain ⟨ z₀, hz₀₁, hz₀₂ ⟩ := hf_zero
      have hg_zero : ∀ᶠ z in nhds z₀, (g : ℂ → ℂ) z = 0 := by
        filter_upwards [ IsOpen.mem_nhds ( Metric.isOpen_ball ) hz₀₁, ( f.2 z₀ ( by simpa using hz₀₁ ) |> AnalyticAt.continuousAt |> ContinuousAt.eventually_ne <| hz₀₂ ) ] with z hz₁ hz₂ using by simpa [ hz₂ ] using hfg_zero z hz₁;
      have hg_zero_all : ∀ z ∈ Metric.ball 0 1, (g : ℂ → ℂ) z = 0 := by
        have h_connected : IsPreconnected (Metric.ball (0 : ℂ) 1) := by
          exact convex_ball _ _ |> Convex.isPreconnected
        apply_rules [ AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero ];
        exact g.2;
      exact Or.inr hg_zero_all;
    · exact Or.inl fun z hz => Classical.not_not.1 fun h => hf_zero ⟨ z, hz, h ⟩
  cases' hfg_zero_or with hf_zero hg_zero
  · left; exact (by
    convert Ideal.Quotient.eq_zero_iff_mem.mpr _;
    exact fun z hz => hf_zero z hz)
  · right; exact (by
    rw [ hg, Ideal.Quotient.eq_zero_iff_mem ] ; exact hg_zero;)

/-- `𝒪(𝔻)` is an integral domain. -/
instance OD_isDomain : IsDomain OD :=
  NoZeroDivisors.to_isDomain OD

/-- `ℛ_ℝ` is an integral domain (a subring of the domain `𝒪(𝔻)`). -/
instance RRsub_isDomain : IsDomain RRsub := by
  haveI : Nontrivial RRsub := RRsub.subtype.domain_nontrivial
  haveI : NoZeroDivisors RRsub :=
    RRsub.subtype_injective.noZeroDivisors RRsub.subtype (map_zero _) (fun a b => map_mul _ a b)
  exact NoZeroDivisors.to_isDomain RRsub

/-! ## The coefficient homomorphism is injective -/

/-
**`coeffHom` is injective.** An element of `ℛ_ℝ` all of whose Taylor
coefficients vanish is `0` (identity theorem: a power series vanishing to
infinite order at `0` is identically `0` on the connected disk).
-/
theorem coeffHom_injective : Function.Injective coeffHom := by
  intro x y hxy
  have h_taylor : ∀ n, ODtaylorCoeff (RRsub.subtype x) n = ODtaylorCoeff (RRsub.subtype y) n := by
    intro n
    have := congr_arg (fun p => PowerSeries.coeff (R := ℤ) n p) hxy
    simp [coeff_coeffHom] at this
    exact (by
    rw [ ← intCoeff_spec, ← intCoeff_spec, this ])
  have h_eq : RRsub.subtype x = RRsub.subtype y := by
    obtain ⟨ f, hf ⟩ := Ideal.Quotient.mk_surjective ( RRsub.subtype x ) ; obtain ⟨ g, hg ⟩ := Ideal.Quotient.mk_surjective ( RRsub.subtype y ) ; simp_all +decide [ ODtaylorCoeff_mk ] ;
    -- Since $f$ and $g$ are analytic on the disk and their Taylor coefficients are equal, they must be equal.
    have h_eq : ∀ z ∈ Metric.ball 0 1, (f : ℂ → ℂ) z = (g : ℂ → ℂ) z := by
      have h_eq : ∀ n : ℕ, taylorCoeff (f : ℂ → ℂ) n = taylorCoeff (g : ℂ → ℂ) n := by
        intro n; have := h_taylor n; rw [ ← ODtaylorCoeff_mk f, ← ODtaylorCoeff_mk g ] at *; aesop;
      intro z hz;
      have := analyticOnNhd_𝔻_hasSum ( f.2 ) hz; have := analyticOnNhd_𝔻_hasSum ( g.2 ) hz; simp_all +decide [ taylorCoeff ] ;
      exact HasSum.unique ‹_› ‹_›;
    exact Subtype.ext <| by rw [ ← hf, ← hg ] ; exact Ideal.Quotient.eq.2 <| mem_vanishIdeal.2 fun z hz => by simpa [ sub_eq_zero ] using h_eq z hz;
  exact RRsub.subtype_injective h_eq

theorem eq_zero_of_intCoeff_eq_zero {x : RRsub} (h : ∀ n, intCoeff x n = 0) : x = 0 := by
  convert coeffHom_injective ?_;
  ext n; simp [h]

/-! ## The kernel of the constant-term homomorphism is `(z)` -/

/-
**`ℛ_ℝ/(z) ≅ ℤ`.** The kernel of `ev₀ : ℛ_ℝ → ℤ` is the principal ideal
generated by `z`.
-/
theorem ker_ev0RR : RingHom.ker ev0RR = Ideal.span {zElt} := by
  refine' le_antisymm _ _;
  · exact fun x hx => Ideal.mem_span_singleton.mpr ( exists_zElt_factor x ( RingHom.mem_ker.mp hx ) );
  · rw [ Ideal.span_le, Set.singleton_subset_iff ] ; aesop

end RequestProject