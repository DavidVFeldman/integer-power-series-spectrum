import SpectrumFormalization.Spectrum

/-!
# Units of `ℛ_ℝ` (recalled from Paper I, real case)

We record the real-coefficient analogue of Proposition `prop:units`: an element
of `ℛ_ℝ` is a unit iff it is nowhere vanishing on `𝔻` (a unit of `𝒪(𝔻)`) and its
constant term is a unit of `ℤ` (i.e. `±1`). The engine is a generic
"reciprocal has coefficients in the subring" lemma, valid for any subring
`S ⊆ ℂ` (it specializes to `ℤ` and to `ℤ[i]`).
-/

open Complex Weierstrass

namespace RequestProject

/-
**Reciprocal coefficient lemma (generic).** If `f` is analytic at `0`, all
its Taylor coefficients lie in a subring `S ⊆ ℂ`, and `f 0` is a unit of `S`,
then the reciprocal `1/f` also has all Taylor coefficients in `S`.
-/
theorem IsSubringCoeffs.inv {S : Subring ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfc : IsSubringCoeffs S f) {u₀ : S} (hu₀ : IsUnit u₀)
    (hf0 : f 0 = (u₀ : ℂ)) : IsSubringCoeffs S (fun z => (f z)⁻¹) := by
  intro m
  induction' m using Nat.strong_induction_on with m ih;
  have h_inv : taylorCoeff (fun z => (f z) * (f z)⁻¹) m = if m = 0 then 1 else 0 := by
    have h_inv : taylorCoeff (fun z => (f z) * (f z)⁻¹) m = taylorCoeff (fun _ => 1 : ℂ → ℂ) m := by
      apply taylorCoeff_congr;
      filter_upwards [ hf.continuousAt.eventually_ne ( show f 0 ≠ 0 from hf0.symm ▸ by simp [ hu₀.ne_zero ] ) ] with z hz using mul_inv_cancel₀ hz;
    rw [ h_inv, RequestProject.taylorCoeff_one ];
  have h_inv : taylorCoeff (fun z => (f z) * (f z)⁻¹) m = ∑ i ∈ Finset.range (m + 1), taylorCoeff f i * taylorCoeff (fun z => (f z)⁻¹) (m - i) := by
    convert taylorCoeff_mul_eq hf ( hf.inv ( show f 0 ≠ 0 from ?_ ) ) m using 1;
    cases hu₀ ; aesop;
  obtain ⟨ v, hv ⟩ := hu₀.exists_right_inv;
  have h_inv : taylorCoeff (fun z => (f z)⁻¹) m = v * ((if m = 0 then 1 else 0) - ∑ i ∈ Finset.range m, taylorCoeff f (i + 1) * taylorCoeff (fun z => (f z)⁻¹) (m - (i + 1))) := by
    simp_all +decide [ Finset.sum_range_succ', taylorCoeff_zero_eq ];
    rw [ ← ‹∑ k ∈ Finset.range m, taylorCoeff f ( k + 1 ) * taylorCoeff ( fun z => ( f z ) ⁻¹ ) ( m - ( k + 1 ) ) + ↑u₀ * taylorCoeff ( fun z => ( f z ) ⁻¹ ) m = if m = 0 then 1 else 0› ] ; ring;
    simp_all +decide [ mul_comm, Subtype.ext_iff ];
  simp_all +decide [ Finset.sum_range_succ', taylorCoeff_zero_eq ];
  exact S.mul_mem v.2 ( S.sub_mem ( by split_ifs <;> simp +decide [ * ] ) ( S.sum_mem fun i hi => S.mul_mem ( hfc _ ) ( ih _ <| Nat.sub_lt ( Nat.pos_of_ne_zero <| by aesop ) <| Nat.succ_pos _ ) ) )

/-
**Proposition `prop:units` (real case).** An element `x` of `ℛ_ℝ` is a unit
iff it is a unit of `𝒪(𝔻)` (nowhere vanishing on `𝔻`) and its constant term
`ev₀ x` is a unit of `ℤ` (that is, `±1`).
-/
theorem units_RRsub (x : RRsub) :
    IsUnit x ↔ IsUnit (RRsub.subtype x) ∧ IsUnit (ev0RR x) := by
  constructor <;> intro h;
  · exact ⟨ h.map _, h.map _ ⟩;
  · -- Let's obtain the function f from the hypothesis h.
    obtain ⟨f, hf⟩ : ∃ f : diskAnalytic, IsIntegerCoeffs f ∧ ODmk f = RRsub.subtype x := by
      exact mem_RRsub.mp x.2;
    -- From `h1 : IsUnit (RRsub.subtype x)`, we get `hne : ∀ z ∈ 𝔻, (f:ℂ→ℂ) z ≠ 0`.
    have hne : ∀ z ∈ 𝔻, (f : ℂ → ℂ) z ≠ 0 := by
      convert nonvanishing_of_isUnit_ODmk _;
      aesop;
    -- From `h2 : IsUnit (ev0RR x)`, we get `u₀ := (⟨(f:ℂ→ℂ) 0, ⟨intCoeff x 0, by ...⟩⟩ : (Int.castRingHom ℂ).range)` and `IsUnit u₀`.
    obtain ⟨u₀, hu₀⟩ : ∃ u₀ : (Int.castRingHom ℂ).range, IsUnit u₀ ∧ (f : ℂ → ℂ) 0 = u₀ := by
      obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℤ, IsUnit u₀ ∧ (f : ℂ → ℂ) 0 = (u₀ : ℂ) := by
        have h_const : (f : ℂ → ℂ) 0 = (intCoeff x 0 : ℂ) := by
          convert intCoeff_spec x 0 |> Eq.symm using 1;
          rw [ ← hf.2, ODtaylorCoeff_mk, taylorCoeff_zero_eq ];
        exact ⟨ _, h.2, h_const ⟩;
      simp_all +decide [ isUnit_iff_exists_inv ];
      obtain ⟨ b, hb ⟩ := hu₀.1; use b; simp_all +decide [ Subtype.ext_iff ] ;
      exact_mod_cast hb;
    -- Let `g := fun z => ((f:ℂ→ℂ) z)⁻¹` be the inverse function.
    obtain ⟨g, hg⟩ : ∃ g : diskAnalytic, IsIntegerCoeffs g ∧ ∀ z ∈ 𝔻, (g : ℂ → ℂ) z * (f : ℂ → ℂ) z = 1 := by
      use ⟨fun z => ((f : ℂ → ℂ) z)⁻¹, AnalyticOnNhd.inv f.2 hne⟩;
      exact ⟨ IsSubringCoeffs.inv ( analyticAt_zero_of_mem_diskAnalytic f.2 ) hf.1 hu₀.1 hu₀.2, fun z hz => inv_mul_cancel₀ ( hne z hz ) ⟩;
    -- Let `y := ⟨ODmk ⟨g, hg_an⟩, ⟨⟨g, hg_an⟩, hg_int, rfl⟩⟩ : RRsub`.
    obtain ⟨y, hy⟩ : ∃ y : RRsub, RRsub.subtype y * RRsub.subtype x = 1 := by
      use ⟨ODmk g, by
        exact ⟨ g, hg.1, rfl ⟩⟩
      generalize_proofs at *;
      rw [ ← hf.2 ];
      exact ODmk_eq_iff.mpr fun z hz => by simpa [ mul_comm ] using hg.2 z hz;
    exact isUnit_of_dvd_one ( dvd_of_mul_left_eq _ <| Subtype.ext hy )

/-- **Structure of type-(iii) maximal ideals, part (ii).** An element `f = 1 + zF`
of `ℛ_ℝ` (constant term `1`) is a unit iff it is a unit of `𝒪(𝔻)` (nowhere
vanishing on `𝔻`); the constant term `1 ∈ ℤˣ` is automatic. -/
theorem isUnit_iff_isUnit_subtype_of_ev0_eq_one (x : RRsub) (hx0 : ev0RR x = 1) :
    IsUnit x ↔ IsUnit (RRsub.subtype x) := by
  rw [units_RRsub]
  simp [hx0]

end RequestProject