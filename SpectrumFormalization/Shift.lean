import SpectrumFormalization.Spectrum

/-!
# Division by `z` in `ℛ_ℝ`

An element of `ℛ_ℝ` with constant term `0` is divisible by `z`. This "coefficient
shift" underlies the generation results for prime ideals in `𝔓₁`.
-/

open Complex Weierstrass

namespace RequestProject

/-
Coefficient shift under multiplication by `z`.
-/
theorem taylorCoeff_zmul {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (m : ℕ) :
    taylorCoeff (fun z => z * h z) (m + 1) = taylorCoeff h m := by
  have := @ RequestProject.taylorCoeff_mul_eq ( fun z => z ) h ( analyticAt_id ) hh ( m + 1 ) ; simp_all +decide [ Finset.sum_range_succ ] ;
  simp_all +decide [ taylorCoeff_id ];
  grind

/-
**Division by `z`.** An element of `ℛ_ℝ` with constant term `0` is divisible
by `z`.
-/
theorem exists_zElt_factor (x : RRsub) (h : ev0RR x = 0) :
    ∃ y : RRsub, x = zElt * y := by
  revert x h;
  -- Let `f` be the representative of `x` in `diskAnalytic`.
  intro x hx
  obtain ⟨f, hf⟩ : ∃ f : diskAnalytic, IsIntegerCoeffs (f : ℂ → ℂ) ∧ ODmk f = RRsub.subtype x ∧ (f : ℂ → ℂ) 0 = 0 := by
    obtain ⟨f, hf⟩ : ∃ f : diskAnalytic, IsIntegerCoeffs (f : ℂ → ℂ) ∧ ODmk f = RRsub.subtype x := by
      exact mem_RRsub.mp x.2;
    refine' ⟨ f, hf.1, hf.2, _ ⟩;
    convert hx using 1;
    rw [ ← @Int.cast_inj ℂ ] ; simp +decide [ ← hf.2, ev0RR_eq, intCoeff_spec ];
    rw [ taylorCoeff_zero_eq ];
  -- Let `uf := dslope (f:ℂ→ℂ) 0`.
  set uf : ℂ → ℂ := dslope (f : ℂ → ℂ) 0;
  have huf_an : AnalyticOnNhd ℂ uf 𝔻 := by
    have huf_an : DifferentiableOn ℂ uf (Metric.ball 0 1) := by
      have huf_an : DifferentiableOn ℂ (f : ℂ → ℂ) (Metric.ball 0 1) := by
        exact f.2.differentiableOn.mono ( by simp +decide [ Metric.ball ] );
      apply differentiableOn_dslope (Metric.ball_mem_nhds 0 zero_lt_one) |>.mpr huf_an;
    exact huf_an.analyticOnNhd ( Metric.isOpen_ball );
  have huf_int : IsIntegerCoeffs uf := by
    intro m
    have h_taylor : taylorCoeff uf m = taylorCoeff (f : ℂ → ℂ) (m + 1) := by
      have h_taylor : taylorCoeff (fun z => z * uf z) (m + 1) = taylorCoeff uf m := by
        apply taylorCoeff_zmul;
        exact huf_an 0 ( Metric.mem_ball_self zero_lt_one );
      rw [ ← h_taylor, show ( fun z => z * uf z ) = ( f : ℂ → ℂ ) from funext fun z => ?_ ];
      have := sub_smul_dslope ( f : ℂ → ℂ ) 0 z; aesop;
    rw [h_taylor]
    exact hf.1 (m + 1);
  have huf_eq : (fun z => z * uf z) = (f : ℂ → ℂ) := by
    ext z; simp [uf, dslope];
    by_cases h : z = 0 <;> simp +decide [ h, slope_def_field, hf.2.2 ];
    rw [ mul_div_cancel₀ _ h ];
  -- Set `y : RRsub := ⟨ODmk ⟨uf, huf_an⟩, ⟨⟨uf, huf_an⟩, huf_int, rfl⟩⟩`.
  obtain ⟨y, hy⟩ : ∃ y : RRsub, ODmk ⟨uf, huf_an⟩ = RRsub.subtype y := by
    exact ⟨ ⟨ ODmk ⟨ uf, huf_an ⟩, ⟨ ⟨ uf, huf_an ⟩, huf_int, rfl ⟩ ⟩, rfl ⟩;
  -- Show `x = zElt * y` by `Subtype.ext` (subtype injective): `RRsub.subtype (zElt * y) = RRsub.subtype zElt * ODmk ⟨uf,_⟩`.
  have hxy : RRsub.subtype x = RRsub.subtype zElt * ODmk ⟨uf, huf_an⟩ := by
    rw [ ← hf.2.1 ];
    convert ODmk_eq_iff.mpr _;
    intro z hz; have := psFun_hasSum ( show ∀ n, ‖( if n = 1 then ( 1 : ℂ ) else 0 )‖ ≤ 1 from fun n => by split_ifs <;> norm_num ) hz; simp_all +decide [ funext_iff ] ;
    rw [ ← huf_eq, mul_comm ];
    rw [ mul_comm, ← this.tsum_eq ];
    rw [ tsum_eq_single 1 ] <;> aesop;
  exact ⟨ y, Subtype.ext <| by simpa [ hy ] using hxy ⟩

end RequestProject