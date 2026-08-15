import RequestProject.ConcreteFiber

/-!
# The ring `ℛ_ℝ = ℤ[[z]] ∩ 𝒪(𝔻)` (sequel, Section on notation)

This file introduces the concrete ring `ℛ_ℝ` of the sequel paper *The Prime
Spectrum of Rings of Integer-Coefficient Power Series on the Disk*
(Bannon–Feldman), building directly on the disk-ring infrastructure of Paper I
(`RequestProject.DiskRing`).

We work with a generic "subring of coefficients" predicate `IsSubringCoeffs S f`
("all Taylor coefficients of `f` at `0` lie in the subring `S ⊆ ℂ`"), which
specializes to the Gaussian case (`S = ℤ[i]`, giving Paper I's `ℛ`) and to the
integer case (`S = ℤ`, giving the sequel's `ℛ_ℝ`).
-/

open Complex Weierstrass

namespace RequestProject

/-! ## Generic coefficient-subring predicate -/

/-- All Taylor coefficients of `f` at `0` lie in the subring `S ⊆ ℂ`. -/
def IsSubringCoeffs (S : Subring ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ m : ℕ, taylorCoeff f m ∈ S

theorem isSubringCoeffs_one (S : Subring ℂ) :
    IsSubringCoeffs S (fun _ : ℂ => (1 : ℂ)) := by
  intro m
  rw [taylorCoeff_one]
  by_cases h : m = 0
  · simp only [h, if_true]; exact S.one_mem
  · simp only [h, if_false]; exact S.zero_mem

theorem isSubringCoeffs_zero (S : Subring ℂ) :
    IsSubringCoeffs S (fun _ : ℂ => (0 : ℂ)) := by
  intro m
  have h0 : taylorCoeff (fun _ : ℂ => (0 : ℂ)) m = 0 := by simp [Weierstrass.taylorCoeff]
  rw [h0]
  exact S.zero_mem

theorem IsSubringCoeffs.add {S : Subring ℂ} {f g : ℂ → ℂ} (hf0 : AnalyticAt ℂ f 0)
    (hg0 : AnalyticAt ℂ g 0) (hf : IsSubringCoeffs S f) (hg : IsSubringCoeffs S g) :
    IsSubringCoeffs S (fun z => f z + g z) := by
  intro m
  rw [Weierstrass.taylorCoeff_add hf0 hg0]
  exact S.add_mem (hf m) (hg m)

theorem IsSubringCoeffs.neg {S : Subring ℂ} {f : ℂ → ℂ}
    (hf : IsSubringCoeffs S f) : IsSubringCoeffs S (fun z => -f z) := by
  intro m
  rw [taylorCoeff_neg]
  exact S.neg_mem (hf m)

theorem IsSubringCoeffs.mul {S : Subring ℂ} {f g : ℂ → ℂ} (hf0 : AnalyticAt ℂ f 0)
    (hg0 : AnalyticAt ℂ g 0) (hf : IsSubringCoeffs S f) (hg : IsSubringCoeffs S g) :
    IsSubringCoeffs S (fun z => f z * g z) := by
  intro m
  rw [taylorCoeff_mul_eq hf0 hg0]
  exact S.sum_mem (fun i _ => S.mul_mem (hf i) (hg (m - i)))

/-- The subring of `diskAnalytic` of functions all of whose Taylor coefficients
at `0` lie in `S`. -/
def coeffSubring (S : Subring ℂ) : Subring diskAnalytic where
  carrier := {f | IsSubringCoeffs S (f : ℂ → ℂ)}
  mul_mem' {a b} ha hb :=
    IsSubringCoeffs.mul (analyticAt_zero_of_mem_diskAnalytic a.2)
      (analyticAt_zero_of_mem_diskAnalytic b.2) ha hb
  one_mem' := isSubringCoeffs_one S
  add_mem' {a b} ha hb :=
    IsSubringCoeffs.add (analyticAt_zero_of_mem_diskAnalytic a.2)
      (analyticAt_zero_of_mem_diskAnalytic b.2) ha hb
  zero_mem' := isSubringCoeffs_zero S
  neg_mem' ha := IsSubringCoeffs.neg ha

theorem mem_coeffSubring {S : Subring ℂ} {f : diskAnalytic} :
    f ∈ coeffSubring S ↔ IsSubringCoeffs S (f : ℂ → ℂ) := Iff.rfl

/-! ## The integer ring `ℛ_ℝ` -/

/-- The predicate that all Taylor coefficients of `f` at `0` are (rational)
integers. -/
def IsIntegerCoeffs (f : ℂ → ℂ) : Prop :=
  IsSubringCoeffs (Int.castRingHom ℂ).range f

/-- `ℛ_ℝ = ℤ[[z]] ∩ 𝒪(𝔻)`, realized as the image in `OD` of the subring of
`diskAnalytic` of functions with integer Taylor coefficients. -/
def RRsub : Subring OD := (coeffSubring (Int.castRingHom ℂ).range).map ODmk

theorem mem_RRsub {x : OD} :
    x ∈ RRsub ↔ ∃ f : diskAnalytic, IsIntegerCoeffs (f : ℂ → ℂ) ∧ ODmk f = x := by
  simp only [RRsub, Subring.mem_map, mem_coeffSubring]
  rfl

end RequestProject
