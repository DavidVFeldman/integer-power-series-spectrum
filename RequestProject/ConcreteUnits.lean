import RequestProject.DiskRing

/-!
# Units of `ℛ` (Section 5, Proposition `prop:units`)

Working with the concrete rings `OD = 𝒪(𝔻)` and `Rsub = ℛ` built in
`RequestProject.DiskRing`, we prove Proposition `prop:units`: an element of `ℛ`
is a unit iff it is a unit of `𝒪(𝔻)` (equivalently, nowhere vanishing on `𝔻`)
and its value at `0` is a unit of the Gaussian integers `ℤ[i]`.
-/

open Complex Weierstrass

namespace RequestProject

/-- Evaluation at `0` as a ring homomorphism on `OD = 𝒪(𝔻)`; well-defined since
representatives agreeing on `𝔻` agree at `0 ∈ 𝔻`. -/
noncomputable def ODeval0 : OD →+* ℂ :=
  Ideal.Quotient.lift vanishIdeal
    ((Pi.evalRingHom (fun _ : ℂ => ℂ) 0).comp diskAnalytic.subtype)
    (fun _ ha => ha 0 (Metric.mem_ball_self one_pos))

@[simp] theorem ODeval0_mk (f : diskAnalytic) :
    ODeval0 (ODmk f) = (f : ℂ → ℂ) 0 := rfl

/-
If the class of `f` is a unit of `OD`, then `f` is nowhere vanishing on `𝔻`.
-/
theorem nonvanishing_of_isUnit_ODmk {f : diskAnalytic} (h : IsUnit (ODmk f)) :
    ∀ z ∈ 𝔻, (f : ℂ → ℂ) z ≠ 0 := by
  intro z hz;
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective h.unit.inv;
  have hfg : (f : ℂ → ℂ) z * (g : ℂ → ℂ) z = 1 := by
    have hfg : ODmk (f * g) = 1 := by
      simp_all +decide [ IsUnit.mul_val_inv ];
    convert ODmk_eq_iff.mp hfg z hz using 1;
  aesop

/-
**Gaussian reciprocal coefficients.** If `f` is analytic at `0`, has all
Taylor coefficients in `ℤ[i]`, and `f 0` is a unit of `ℤ[i]` (say `f 0 = w₀`
with `w₀` a unit), then the reciprocal `1/f` also has all Taylor coefficients in
`ℤ[i]`.
-/
theorem isGaussianCoeffs_inv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfg : IsGaussianCoeffs f) {w₀ : GaussianInt} (hw₀ : IsUnit w₀)
    (hf0 : f 0 = GaussianInt.toComplex w₀) :
    IsGaussianCoeffs (fun z => (f z)⁻¹) := by
  obtain ⟨v, hv⟩ : ∃ v : GaussianInt, w₀ * v = 1 := by
    exact hw₀.exists_right_inv;
  intro m
  induction' m using Nat.strong_induction_on with m ih
  generalize_proofs at *; (
  -- By the master identity, we have:
  have h_master : ∑ i ∈ Finset.range (m + 1), taylorCoeff f i * taylorCoeff (fun z => (f z)⁻¹) (m - i) = if m = 0 then 1 else 0 := by
    have h_master : taylorCoeff (fun z => f z * (f z)⁻¹) m = if m = 0 then 1 else 0 := by
      have h_master : taylorCoeff (fun z => f z * (f z)⁻¹) m = taylorCoeff (fun _ => 1 : ℂ → ℂ) m := by
        apply Weierstrass.taylorCoeff_congr
        generalize_proofs at *; (
        filter_upwards [ hf.continuousAt.eventually_ne ( show f 0 ≠ 0 from hf0.symm ▸ by simpa [ GaussianInt.toComplex_inj ] using hw₀.ne_zero ) ] with z hz using mul_inv_cancel₀ hz)
      generalize_proofs at *; (
      exact h_master.trans ( taylorCoeff_one m ))
    generalize_proofs at *; (
    rw [ ← h_master, taylorCoeff_mul_eq hf ( show AnalyticAt ℂ ( fun z => ( f z ) ⁻¹ ) 0 from ?_ ) ];
    exact hf.inv ( by rw [ hf0 ] ; exact by simpa [ GaussianInt.toComplex_inj ] using hw₀.ne_zero ))
  generalize_proofs at *; (
  -- By the master identity, we can solve for taylorCoeff (fun z => (f z)⁻¹) m.
  have h_solve : taylorCoeff (fun z => (f z)⁻¹) m = (GaussianInt.toComplex v) * ((if m = 0 then 1 else 0) - ∑ i ∈ Finset.range m, taylorCoeff f (i + 1) * taylorCoeff (fun z => (f z)⁻¹) (m - (i + 1))) := by
    simp_all +decide [ Finset.sum_range_succ', taylorCoeff_zero_eq ];
    rw [ ← h_master, add_sub_cancel_left, mul_comm ];
    rw [ mul_right_comm, ← map_mul, hv, map_one, one_mul ]
  generalize_proofs at *; (
  choose! x hx using hfg; choose! y hy using ih; simp_all +decide [ Finset.sum_range ] ;
  use v * ((if m = 0 then 1 else 0) - ∑ i : Fin m, x (i.val + 1) * y (m - (i.val + 1))) ; simp +decide [ ← hx ] ;
  grind)))

/-
**Proposition `prop:units`.** An element `x` of `ℛ` is a unit if and only if
it is a unit of `𝒪(𝔻)` (i.e. nowhere vanishing on `𝔻`) and its value at `0` is a
unit of the Gaussian integers `ℤ[i]`.
-/
theorem units_Rsub (x : Rsub) :
    IsUnit x ↔ IsUnit (Rsub.subtype x) ∧
      ∃ w : GaussianInt, IsUnit w ∧ ODeval0 (Rsub.subtype x) = GaussianInt.toComplex w := by
  constructor;
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have h_unit : IsUnit (Rsub.subtype x) := by
      exact IsUnit.map ( Rsub.subtype ) hx;
    obtain ⟨w, hw⟩ : ∃ w : GaussianInt, ODeval0 (Rsub.subtype x) = GaussianInt.toComplex w := by
      obtain ⟨ f, hf ⟩ := x.2;
      have := hf.1 0; simp_all +decide [ taylorCoeff_zero_eq ] ;
      obtain ⟨ w, hw ⟩ := this; use w; simp +decide [ ← hw, ← hf.2, ODeval0_mk ] ;
    obtain ⟨w', hw'⟩ : ∃ w' : GaussianInt, ODeval0 (Rsub.subtype y) = GaussianInt.toComplex w' := by
      obtain ⟨ F, hF, hF' ⟩ := y.2;
      have := hF 0; simp_all +decide [ taylorCoeff_zero_eq ] ;
      exact ⟨ this.choose, by simpa [ ← hF' ] using this.choose_spec.symm ⟩;
    have h_unit : ODeval0 (Rsub.subtype x) * ODeval0 (Rsub.subtype y) = 1 := by
      rw [ ← map_mul, show Rsub.subtype x * Rsub.subtype y = 1 from by simpa using congr_arg Rsub.subtype hy ] ; norm_num [ ODeval0_mk ];
    simp_all +decide [ GaussianInt.toComplex_inj ];
    exact isUnit_iff_exists_inv.mpr ⟨ w', by simpa [ ← @GaussianInt.toComplex_inj ] using h_unit ⟩;
  · intro hx;
    -- Let $y$ be the element in $Rsub$ such that $ODmk y = x$.
    obtain ⟨y, hy⟩ : ∃ y : Rpre, ODmk y = x := by
      obtain ⟨ y, hy ⟩ := x.2;
      exact ⟨ ⟨ y, hy.1 ⟩, hy.2 ⟩;
    -- Let $g(z) = \frac{1}{f(z)}$.
    obtain ⟨g, hg⟩ : ∃ g : diskAnalytic, IsGaussianCoeffs (g : ℂ → ℂ) ∧ ∀ z ∈ 𝔻, (g : ℂ → ℂ) z * (y : ℂ → ℂ) z = 1 := by
      obtain ⟨w, hw, hw'⟩ := hx.right
      have h_nonvanishing : ∀ z ∈ Metric.ball 0 1, (y : ℂ → ℂ) z ≠ 0 := by
        have := nonvanishing_of_isUnit_ODmk ( show IsUnit ( ODmk y ) from ?_ ) ; aesop;
        convert hx.1 using 1
      have h_gaussian : IsGaussianCoeffs (fun z => (y : ℂ → ℂ) z) := by
        exact y.2
      have h_inv : IsGaussianCoeffs (fun z => ((y : ℂ → ℂ) z)⁻¹) := by
        apply isGaussianCoeffs_inv;
        exact analyticAt_zero_of_mem_diskAnalytic y.1.2;
        bv_omega;
        exact hw;
        grind +suggestions
      use ⟨fun z => ((y : ℂ → ℂ) z)⁻¹, by
        exact AnalyticOnNhd.inv ( y.1.2 ) ( by aesop )⟩
      generalize_proofs at *;
      exact ⟨ h_inv, fun z hz => inv_mul_cancel₀ ( h_nonvanishing z hz ) ⟩;
    -- Since $g$ is in $Rpre$, we have $ODmk g \in Rsub$.
    have hg_Rsub : ODmk g ∈ Rsub := by
      exact ⟨ g, hg.1, rfl ⟩;
    -- Since $g$ is in $Rpre$, we have $ODmk g * ODmk y = 1$.
    have hg_mul_y : ODmk g * ODmk y = 1 := by
      convert ODmk_eq_iff.mpr _;
      aesop;
    obtain ⟨z, hz⟩ : ∃ z : Rsub, ODmk g = z := by
      exact ⟨ ⟨ _, hg_Rsub ⟩, rfl ⟩;
    have hz_inv : z * x = 1 := by
      exact Subtype.ext <| by aesop;
    exact isUnit_of_dvd_one ( dvd_of_mul_left_eq _ hz_inv )

end RequestProject