import RequestProject.ConcreteUnits

/-!
# The arithmetic fiber of `ℛ` (Section 5, Proposition `prop:fiber`)

Working with the concrete rings `OD = 𝒪(𝔻)` and `Rsub = ℛ`, we formalize the core
of Proposition `prop:fiber`: evaluation at `0` is a surjective ring homomorphism
`ev0R : ℛ → ℤ[i]` whose kernel is the augmentation ideal
`𝔫₀ = {g ∈ ℛ : g(0) = 0}`, and consequently `ℛ / 𝔫₀ ≅ ℤ[i]`.
-/

open Complex Weierstrass

namespace RequestProject

/-
For an element of `ℛ`, its value at `0` is a Gaussian integer.
-/
theorem ODeval0_mem_range (x : Rsub) :
    ODeval0 (Rsub.subtype x) ∈ GaussianInt.toComplex.range := by
  obtain ⟨ F, hF, hFx ⟩ := ( Subring.mem_map ).mp x.2;
  convert hF 0 using 1;
  convert ODeval0_mk F using 1;
  · exact hFx.symm ▸ rfl;
  · exact taylorCoeff_zero_eq _

/-- The subring of `ℂ` of Gaussian integers is ring-isomorphic to `ℤ[i]`. -/
noncomputable def rangeEquivGaussian : GaussianInt ≃+* GaussianInt.toComplex.range :=
  RingEquiv.ofBijective GaussianInt.toComplex.rangeRestrict
    ⟨fun a b h => GaussianInt.toComplex_injective (by simpa using Subtype.ext_iff.mp h),
     GaussianInt.toComplex.rangeRestrict_surjective⟩

theorem rangeEquivGaussian_apply (w : GaussianInt) :
    (rangeEquivGaussian w : ℂ) = GaussianInt.toComplex w := rfl

/-- **Evaluation at `0` on `ℛ`, valued in `ℤ[i]`.** This is the surjection
`ev₀ : ℛ → ℤ[i]` of Proposition `prop:fiber`. -/
noncomputable def ev0R : Rsub →+* GaussianInt :=
  rangeEquivGaussian.symm.toRingHom.comp
    ((ODeval0.comp Rsub.subtype).codRestrict GaussianInt.toComplex.range ODeval0_mem_range)

/-
`ev0R` computes the value at `0`, viewed in `ℂ` via `GaussianInt.toComplex`.
-/
theorem toComplex_ev0R (x : Rsub) :
    GaussianInt.toComplex (ev0R x) = ODeval0 (Rsub.subtype x) := by
  convert congr_arg Subtype.val ( RingEquiv.apply_symm_apply rangeEquivGaussian _ ) using 1

/-
`ev0R` is surjective: every Gaussian integer is the value at `0` of an element
of `ℛ` (namely the corresponding constant function).
-/
theorem ev0R_surjective : Function.Surjective ev0R := by
  intro w
  use ⟨ODmk ⟨fun _ => GaussianInt.toComplex w, analyticOnNhd_const⟩, by
    refine' ⟨ ⟨ fun _ => GaussianInt.toComplex w, analyticOnNhd_const ⟩, _, _ ⟩ <;> norm_num [ Subring.mem_map ];
    intro m; by_cases hm : m = 0 <;> simp +decide [ hm, taylorCoeff_zero_eq ] ;
    induction m <;> simp_all +decide [ taylorCoeff ];
    simp +decide [ iteratedDeriv_succ' ]⟩
  generalize_proofs at *;
  exact GaussianInt.toComplex_inj.mp ( by simp [ toComplex_ev0R ] )

/-- The augmentation ideal `𝔫₀ = {g ∈ ℛ : g(0) = 0}` of `ℛ`, as the kernel of
evaluation at `0`. -/
noncomputable def augIdeal : Ideal Rsub := RingHom.ker ev0R

/-
The augmentation ideal consists exactly of the elements of `ℛ` vanishing at
`0`.
-/
theorem mem_augIdeal (x : Rsub) :
    x ∈ augIdeal ↔ ODeval0 (Rsub.subtype x) = 0 := by
  rw [ ← toComplex_ev0R x ];
  simp +decide [ augIdeal ]

/-- **Proposition `prop:fiber` (core).** `ℛ / 𝔫₀ ≅ ℤ[i]`. -/
noncomputable def fiberEquiv : Rsub ⧸ augIdeal ≃+* GaussianInt :=
  RingHom.quotientKerEquivOfSurjective ev0R_surjective

end RequestProject