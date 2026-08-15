import SpectrumFormalization.Units
import WeierstrassFormalization.AssociateFactorization

/-!
# The unit-quotient lemma (`lem:unitquotient`)

Two elements of `ℛ_ℝ` with constant term `1` and the same zero divisor on `𝔻`
differ by a unit of `ℛ_ℝ`. This is the analytic heart of the completeness of the
zero-divisor invariant `𝒵` on `𝔓₁`.
-/

open Complex Weierstrass

namespace RequestProject

/-! ## The zero-divisor of an element of `OD` -/

/-- The order of vanishing at `a ∈ 𝔻` of (any representative of) a class in `OD`.
Well-defined because representatives agree on `𝔻`, a neighborhood of `a`. -/
noncomputable def ODorder (a : ℂ) (ha : a ∈ 𝔻) (u : OD) : ℕ :=
  Quotient.liftOn' u (fun f : diskAnalytic => analyticOrderNatAt (f : ℂ → ℂ) a) (by
    intro p q h
    have hmem : p - q ∈ vanishIdeal := (Submodule.quotientRel_def _).mp h
    have hEq : (p : ℂ → ℂ) =ᶠ[nhds a] (q : ℂ → ℂ) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds Metric.isOpen_ball ha) ?_
      intro z hz
      have := hmem z hz
      simpa [sub_eq_zero] using this
    show analyticOrderNatAt (p : ℂ → ℂ) a = analyticOrderNatAt (q : ℂ → ℂ) a
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hEq])

@[simp] theorem ODorder_mk (f : diskAnalytic) (a : ℂ) (ha : a ∈ 𝔻) :
    ODorder a ha (ODmk f) = analyticOrderNatAt (f : ℂ → ℂ) a := rfl

/-- Two elements of `ℛ_ℝ` have the same zero divisor on `𝔻`. -/
def SameZeroDivisor (x y : RRsub) : Prop :=
  ∀ a (ha : a ∈ 𝔻), ODorder a ha (RRsub.subtype x) = ODorder a ha (RRsub.subtype y)

/-! ## Integer coefficients of a quotient -/

/-
If `fprod = g · u` near `0`, `g` and `fprod` have coefficients in `S`, and
`g 0 = 1`, then `u` has coefficients in `S` (triangular convolution recursion).
-/
theorem IsSubringCoeffs.of_mul_factor {S : Subring ℂ} {g u fprod : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (hu : AnalyticAt ℂ u 0)
    (hfeq : fprod =ᶠ[nhds 0] fun z => g z * u z)
    (hgc : IsSubringCoeffs S g) (hfc : IsSubringCoeffs S fprod)
    (hg0 : g 0 = 1) : IsSubringCoeffs S u := by
  have h_taylorCoeff_u : ∀ m, taylorCoeff u m = taylorCoeff fprod m - ∑ i ∈ Finset.range m, taylorCoeff g (i + 1) * taylorCoeff u (m - (i + 1)) := by
    intro m
    have h_taylorCoeff_fprod : taylorCoeff fprod m = ∑ i ∈ Finset.range (m + 1), taylorCoeff g i * taylorCoeff u (m - i) := by
      rw [ taylorCoeff_congr hfeq, taylorCoeff_mul_eq hg hu m ];
    simp_all +decide [ Finset.sum_range_succ', taylorCoeff_zero_eq ];
  intro m
  induction' m using Nat.strong_induction_on with m ih;
  exact h_taylorCoeff_u m ▸ S.sub_mem ( hfc m ) ( S.sum_mem fun i hi => S.mul_mem ( hgc _ ) ( ih _ ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by rintro rfl; simp +decide at hi ) ) ( Nat.succ_pos _ ) ) ) )

/-! ## The unit-quotient lemma -/

/-
**Unit-quotient lemma (`lem:unitquotient`).** If `x, y ∈ ℛ_ℝ` both have
constant term `1` and the same zero divisor on `𝔻`, then `x = u · y` for a unit
`u` of `ℛ_ℝ`.
-/
theorem unit_quotient (x y : RRsub) (hx0 : ev0RR x = 1) (hy0 : ev0RR y = 1)
    (hZ : SameZeroDivisor x y) : ∃ u : RRsub, IsUnit u ∧ x = u * y := by
  revert hZ;
  intro hZ
  obtain ⟨f, hf⟩ := mem_RRsub.mp x.2
  obtain ⟨g, hg⟩ := mem_RRsub.mp y.2
  have hf0 : (f : ℂ → ℂ) 0 = 1 := by
    have hf0 : (f : ℂ → ℂ) 0 = taylorCoeff f 0 := by
      exact taylorCoeff_zero_eq _ ▸ rfl;
    convert hx0 using 1;
    rw [ ← @Int.cast_inj ℂ ] ; simp +decide [ hf0, ev0RR_eq, intCoeff_spec, hf.2 ];
    rw [ ← hf.2, ODtaylorCoeff_mk ]
  have hg0 : (g : ℂ → ℂ) 0 = 1 := by
    convert hy0 using 1;
    rw [ ← @Int.cast_inj ℂ ] ; simp +decide [ hg.2.symm, ev0RR_eq, intCoeff_spec ];
    rw [ taylorCoeff_zero_eq ]
  have hfne : ∃ z ∈ 𝔻, (f : ℂ → ℂ) z ≠ 0 := by
    exact ⟨ 0, by norm_num, by norm_num [ hf0 ] ⟩
  have hgne : ∃ z ∈ 𝔻, (g : ℂ → ℂ) z ≠ 0 := by
    exact ⟨ 0, by norm_num, by norm_num [ hg0 ] ⟩
  have horder : ∀ z ∈ 𝔻, analyticOrderNatAt (f : ℂ → ℂ) z = analyticOrderNatAt (g : ℂ → ℂ) z := by
    intro z hz; specialize hZ z hz; simp_all +decide [ SameZeroDivisor ] ;
    convert hZ using 1 <;> simp +decide [ ← hf.2, ← hg.2, ODorder_mk ]
  have hdiv : MeromorphicOn.divisor ((f : ℂ → ℂ) * (g : ℂ → ℂ)⁻¹) 𝔻 = 0 := by
    apply divisor_mul_inv_eq_zero f.2 g.2 hfne hgne horder
  have ⟨uf, huf_an, huf_ne, huf_eq⟩ := factor_of_divisor_zero f.2 g.2 hgne hfne hdiv
  have hui : IsSubringCoeffs (Int.castRingHom ℂ).range uf := by
    apply IsSubringCoeffs.of_mul_factor (g.2 0 (by simp [mem_𝔻_iff])) (huf_an 0 (by simp [mem_𝔻_iff])) (by
    exact Filter.eventually_of_mem ( Metric.ball_mem_nhds _ zero_lt_one ) huf_eq) hg.1 hf.1 hg0
  have hufe : (uf : ℂ → ℂ) 0 = 1 := by
    have := huf_eq ( Metric.mem_ball_self zero_lt_one ) ; aesop;
  set u : RRsub := ⟨ODmk ⟨uf, huf_an⟩, ⟨⟨uf, huf_an⟩, hui, rfl⟩⟩
  have hu_unit : IsUnit u := by
    refine' units_RRsub u |>.2 ⟨ _, _ ⟩;
    · exact isUnit_ODmk_of_nonvanishing huf_an huf_ne;
    · simp +decide [ ev0RR_eq, intCoeff_spec, ODtaylorCoeff_mk, taylorCoeff_zero_eq, hufe ];
      have := intCoeff_spec u 0; simp_all +decide [ ODtaylorCoeff_mk, taylorCoeff_zero_eq ] ;
      rw [ ODtaylorCoeff_mk ] at this; simp_all +decide [ taylorCoeff_zero_eq ] ;
  have hxu : x = u * y := by
    have hxu : ODmk f = ODmk ⟨uf, huf_an⟩ * ODmk g := by
      apply ODmk_eq_iff.mpr;
      exact fun z hz => by simpa [ mul_comm ] using huf_eq hz;
    exact Subtype.ext <| by aesop;
  use u

end RequestProject