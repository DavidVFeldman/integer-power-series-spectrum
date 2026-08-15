import Mathlib
import WeierstrassFormalization.AssociateFactorization
import RequestProject.RingConsequences

/-!
# The concrete rings `𝒪(𝔻)` and `ℛ` (Section 5)

This file makes the Section 5 ring-theoretic consequences of the paper
*Integer Coefficients Power Series with Prescribed Zero Sets* (Bannon–Feldman)
**unconditional** by building the concrete rings and instantiating the abstract
results of `RequestProject.RingConsequences` at them.

We model:

* `𝒪(𝔻)` — holomorphic functions on the open unit disk — as the quotient `OD`
  of the ring `diskAnalytic` of functions `ℂ → ℂ` analytic on a neighborhood of
  `𝔻`, by the ideal `vanishIdeal` of functions vanishing everywhere on `𝔻`.
  Two representatives are identified precisely when they agree on `𝔻`, so units
  of `OD` are exactly the classes of nowhere-vanishing holomorphic functions.
* `ℛ = ℤ[i][[z]] ∩ 𝒪(𝔻)` — as the subring `Rsub` of `OD`, the image of the
  subring `Rpre` of `diskAnalytic` of functions all of whose Taylor coefficients
  at `0` are Gaussian integers.

The key input is `Weierstrass.associate_factorization` (Proposition
`prop:associate`), which we package into `hasSubringFactorization`
(`HasSubringFactorization Rsub`). Instantiating the abstract theorems yields the
concrete Corollary `cor:ideals` (`ideal_eq_map_comap_OD`) and Proposition
`prop:inject` (`contraction_maximalSpec_injective_OD`).
-/

open Complex Weierstrass

namespace RequestProject

/-! ## The Cauchy product for Taylor coefficients -/

/-
**Cauchy product for Taylor coefficients.** For `f, g` analytic at `0`, the
`m`-th Taylor coefficient of the pointwise product is the convolution of the
Taylor coefficients of the factors.
-/
theorem taylorCoeff_mul_eq {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (m : ℕ) :
    taylorCoeff (fun z => f z * g z) m =
      ∑ i ∈ Finset.range (m + 1), taylorCoeff f i * taylorCoeff g (m - i) := by
  unfold taylorCoeff
  rw [show (fun z => f z * g z) = f * g from rfl,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.cast_choose ℂ hi']
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have h2 : ((m - i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m - i)
  have h3 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-
The `0`-th Taylor coefficient is the value at `0`.
-/
theorem taylorCoeff_zero_eq (f : ℂ → ℂ) : taylorCoeff f 0 = f 0 := by
  unfold taylorCoeff; norm_num [ iteratedDeriv_succ' ] ;

/-
Taylor coefficients of the constant function `1`.
-/
theorem taylorCoeff_one (m : ℕ) :
    taylorCoeff (fun _ : ℂ => (1 : ℂ)) m = if m = 0 then 1 else 0 := by
  unfold taylorCoeff;
  cases m <;> simp +decide [ iteratedDeriv_succ' ]

/-
Taylor coefficients of the identity function `z ↦ z`.
-/
theorem taylorCoeff_id (i : ℕ) :
    taylorCoeff (fun z : ℂ => z) i = if i = 1 then 1 else 0 := by
  unfold taylorCoeff;
  rcases i with ( _ | _ | i ) <;> simp +decide [ div_eq_iff, Nat.factorial_ne_zero, iteratedDeriv_succ' ]

/-
Taylor coefficients are compatible with negation on functions analytic at `0`.
-/
theorem taylorCoeff_neg {m : ℕ} {f : ℂ → ℂ} :
    taylorCoeff (fun z => -f z) m = -taylorCoeff f m := by
  unfold taylorCoeff;
  rw [ iteratedDeriv_eq_iterate ];
  -- Apply the fact that the derivative of a negative function is the negative of the derivative.
  have h_deriv_neg : ∀ m : ℕ, deriv^[m] (fun z => -f z) = fun z => -deriv^[m] f z := by
    intro m; induction m <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
  rw [ h_deriv_neg, iteratedDeriv_eq_iterate ] ; ring

/-! ## Gaussian-integer coefficient sequences -/

/-- The predicate that all Taylor coefficients of `f` at `0` are Gaussian
integers, i.e. lie in the range of `GaussianInt.toComplex`. -/
def IsGaussianCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ m : ℕ, taylorCoeff f m ∈ GaussianInt.toComplex.range

theorem isGaussianCoeffs_one : IsGaussianCoeffs (fun _ : ℂ => (1 : ℂ)) := by
  intro m;
  rcases m with ( _ | m ) <;> simp_all +decide [ taylorCoeff_one ]

theorem isGaussianCoeffs_zero : IsGaussianCoeffs (fun _ : ℂ => (0 : ℂ)) := by
  intro m
  simp [Weierstrass.taylorCoeff]

theorem IsGaussianCoeffs.add {f g : ℂ → ℂ} (hf0 : AnalyticAt ℂ f 0)
    (hg0 : AnalyticAt ℂ g 0) (hf : IsGaussianCoeffs f) (hg : IsGaussianCoeffs g) :
    IsGaussianCoeffs (fun z => f z + g z) := by
  intro m;
  obtain ⟨ z₁, hz₁ ⟩ := hf m
  obtain ⟨ z₂, hz₂ ⟩ := hg m
  have h : taylorCoeff (fun z => f z + g z) m = z₁ + z₂ := by
    rw [ hz₁, hz₂, Weierstrass.taylorCoeff_add hf0 hg0 ];
  exact ⟨ z₁ + z₂, by simp [ h ] ⟩

theorem IsGaussianCoeffs.neg {f : ℂ → ℂ}
    (hf : IsGaussianCoeffs f) : IsGaussianCoeffs (fun z => -f z) := by
  exact fun m => by simpa [ taylorCoeff_neg ] using hf m;

theorem IsGaussianCoeffs.mul {f g : ℂ → ℂ} (hf0 : AnalyticAt ℂ f 0)
    (hg0 : AnalyticAt ℂ g 0) (hf : IsGaussianCoeffs f) (hg : IsGaussianCoeffs g) :
    IsGaussianCoeffs (fun z => f z * g z) := by
  intro m;
  convert Subring.sum_mem _ _;
  convert taylorCoeff_mul_eq hf0 hg0 m using 1;
  exact fun i hi => Subring.mul_mem _ ( hf i ) ( hg ( m - i ) )

/-! ## `diskAnalytic`: functions analytic on the disk -/

/-- The subring of `ℂ → ℂ` of functions analytic on a neighborhood of the open
unit disk `𝔻`. This carries `𝒪(𝔻)` before we quotient by equality on `𝔻`. -/
def diskAnalytic : Subring (ℂ → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ f 𝔻}
  mul_mem' ha hb := ha.mul hb
  one_mem' := analyticOnNhd_const
  add_mem' ha hb := ha.add hb
  zero_mem' := analyticOnNhd_const
  neg_mem' ha := ha.neg

theorem mem_diskAnalytic {f : ℂ → ℂ} : f ∈ diskAnalytic ↔ AnalyticOnNhd ℂ f 𝔻 :=
  Iff.rfl

/-- Every element of `diskAnalytic` is analytic at `0`. -/
theorem analyticAt_zero_of_mem_diskAnalytic {f : ℂ → ℂ} (hf : f ∈ diskAnalytic) :
    AnalyticAt ℂ f 0 :=
  (mem_diskAnalytic.mp hf) 0 (Metric.mem_ball_self one_pos)

/-! ## `vanishIdeal`: functions vanishing on the disk -/

/-- The ideal of `diskAnalytic` of functions vanishing everywhere on `𝔻`. -/
def vanishIdeal : Ideal diskAnalytic where
  carrier := {f | ∀ z ∈ 𝔻, (f : ℂ → ℂ) z = 0}
  add_mem' := by intro a b ha hb z hz; simp [Subring.coe_add, ha z hz, hb z hz]
  zero_mem' := by intro z hz; rfl
  smul_mem' := by intro c a ha z hz; simp [ha z hz]

theorem mem_vanishIdeal {f : diskAnalytic} :
    f ∈ vanishIdeal ↔ ∀ z ∈ 𝔻, (f : ℂ → ℂ) z = 0 :=
  Iff.rfl

/-- `𝒪(𝔻)`: holomorphic functions on the open unit disk, as functions analytic
on `𝔻` modulo equality on `𝔻`. -/
abbrev OD : Type := diskAnalytic ⧸ vanishIdeal

/-- The quotient map `diskAnalytic → OD`. -/
abbrev ODmk : diskAnalytic →+* OD := Ideal.Quotient.mk vanishIdeal

/-
Two representatives give the same element of `OD` iff they agree on `𝔻`.
-/
theorem ODmk_eq_iff {f g : diskAnalytic} :
    ODmk f = ODmk g ↔ ∀ z ∈ 𝔻, (f : ℂ → ℂ) z = (g : ℂ → ℂ) z := by
  convert Ideal.Quotient.eq;
  simp +decide [ sub_eq_zero, mem_vanishIdeal ]

/-! ## `Rpre` and `Rsub = ℛ` -/

/-- The subring of `diskAnalytic` of functions with Gaussian-integer Taylor
coefficients. Its image in `OD` is `ℛ = ℤ[i][[z]] ∩ 𝒪(𝔻)`. -/
def Rpre : Subring diskAnalytic where
  carrier := {f | IsGaussianCoeffs (f : ℂ → ℂ)}
  mul_mem' {a b} ha hb :=
    (IsGaussianCoeffs.mul (analyticAt_zero_of_mem_diskAnalytic a.2)
      (analyticAt_zero_of_mem_diskAnalytic b.2) ha hb)
  one_mem' := isGaussianCoeffs_one
  add_mem' {a b} ha hb :=
    (IsGaussianCoeffs.add (analyticAt_zero_of_mem_diskAnalytic a.2)
      (analyticAt_zero_of_mem_diskAnalytic b.2) ha hb)
  zero_mem' := isGaussianCoeffs_zero
  neg_mem' ha := (IsGaussianCoeffs.neg ha)

theorem mem_Rpre {f : diskAnalytic} : f ∈ Rpre ↔ IsGaussianCoeffs (f : ℂ → ℂ) :=
  Iff.rfl

/-- `ℛ = ℤ[i][[z]] ∩ 𝒪(𝔻)`, realized as the image in `OD` of the subring `Rpre`
of functions with Gaussian-integer Taylor coefficients. -/
def Rsub : Subring OD := Rpre.map ODmk

/-! ## The factorization property for the concrete rings -/

/-
If `u` is analytic on `𝔻` and nowhere vanishing there, then its class in `OD`
is a unit.
-/
theorem isUnit_ODmk_of_nonvanishing {u : ℂ → ℂ} (hu : AnalyticOnNhd ℂ u 𝔻)
    (hune : ∀ z ∈ 𝔻, u z ≠ 0) : IsUnit (ODmk ⟨u, hu⟩) := by
  refine' IsUnit.of_mul_eq_one _ _;
  exact ODmk ⟨ fun z => ( u z ) ⁻¹, by
    exact hu.inv hune ⟩
  generalize_proofs at *;
  convert ODmk_eq_iff.mpr _;
  aesop

/-
**Proposition `prop:associate`** for the concrete rings: every element of
`𝒪(𝔻)` factors as an element of `ℛ` times a unit of `𝒪(𝔻)`.
-/
theorem hasSubringFactorization : HasSubringFactorization Rsub := by
  intro x;
  obtain ⟨af, rfl⟩ := Ideal.Quotient.mk_surjective x;
  by_cases h : ∀ z ∈ Metric.ball 0 1, (af : ℂ → ℂ) z = 0;
  · refine' ⟨ 0, _, 1, _ ⟩;
    · exact ⟨ 0, by simp +decide ⟩;
    · convert Ideal.Quotient.eq_zero_iff_mem.mpr _;
      · norm_num;
      · exact h;
  · obtain ⟨g, u, hg_an, hg_gauss, hu_an, hu_ne, heq⟩ := Weierstrass.associate_factorization af.2 (by
    grind)
    generalize_proofs at *;
    refine' ⟨ _, ⟨ ⟨ g, hg_an ⟩, _, rfl ⟩, _, _ ⟩;
    exact fun m => by obtain ⟨ w, hw ⟩ := hg_gauss m; exact ⟨ w, hw ▸ rfl ⟩;
    exact ( isUnit_ODmk_of_nonvanishing hu_an hu_ne ).unit
    generalize_proofs at *;
    exact ODmk_eq_iff.mpr ( by aesop )

/-! ## Concrete Section 5 consequences -/

/-- **Corollary `cor:ideals`** for the concrete rings: every ideal `I` of `𝒪(𝔻)`
satisfies `I = (I ∩ ℛ) · 𝒪(𝔻)`. -/
theorem ideal_eq_map_comap_OD (I : Ideal OD) :
    I = (I.comap Rsub.subtype).map Rsub.subtype :=
  ideal_eq_map_comap hasSubringFactorization I

/-- **Proposition `prop:inject`** for the concrete rings: the contraction map
`φ : MaxSpec(𝒪(𝔻)) → Spec(ℛ)`, `𝔪 ↦ 𝔪 ∩ ℛ`, is injective. -/
theorem contraction_maximalSpec_injective_OD :
    Function.Injective
      (fun m : {m : Ideal OD // m.IsMaximal} => m.1.comap Rsub.subtype) :=
  contraction_maximalSpec_injective hasSubringFactorization

end RequestProject