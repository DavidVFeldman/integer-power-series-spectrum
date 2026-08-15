import SpectrumFormalization.PointEval
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The coefficient homomorphism `ℛ_ℝ → ℤ⟦z⟧` and reduction mod `p`

We package the Taylor coefficients of an element of `ℛ_ℝ` into a formal power
series with integer coefficients. Since the Taylor coefficients of a product are
the Cauchy convolution of the factors' coefficients (`taylorCoeff_mul_eq`), this
assignment is an *injective ring homomorphism* `coeffHom : ℛ_ℝ → ℤ⟦z⟧`.

Composing with coefficientwise reduction gives, for a prime `p`, a *surjective*
ring homomorphism `redHom p : ℛ_ℝ → 𝔽ₚ⟦z⟧` whose kernel is the ideal `(p)`. This
identifies `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`, the engine behind the trichotomy of maximal ideals
and the classification of primes outside `𝔓₁`.
-/

open Complex Weierstrass

namespace RequestProject

/-! ## Well-defined Taylor coefficients on `OD` -/

/-- The `n`-th Taylor coefficient of (any representative of) a class in `OD`.
Well-defined because representatives agree on `𝔻`, a neighborhood of `0`. -/
noncomputable def ODtaylorCoeff (x : OD) (n : ℕ) : ℂ :=
  Quotient.liftOn' x (fun f : diskAnalytic => taylorCoeff (f : ℂ → ℂ) n) (by
    intro a b h
    apply taylorCoeff_congr
    have hmem : a - b ∈ vanishIdeal := by
      rw [Submodule.quotientRel_def] at h; exact h
    have hagree : ∀ z ∈ 𝔻, (a : ℂ → ℂ) z = (b : ℂ → ℂ) z := by
      intro z hz; simpa [sub_eq_zero] using hmem z hz
    exact Filter.eventuallyEq_of_mem
      (IsOpen.mem_nhds Metric.isOpen_ball (Metric.mem_ball_self one_pos))
      (fun z hz => hagree z hz))

@[simp] theorem ODtaylorCoeff_mk (f : diskAnalytic) (n : ℕ) :
    ODtaylorCoeff (ODmk f) n = taylorCoeff (f : ℂ → ℂ) n := rfl

theorem ODtaylorCoeff_add (u v : OD) (n : ℕ) :
    ODtaylorCoeff (u + v) n = ODtaylorCoeff u n + ODtaylorCoeff v n := by
  obtain ⟨a, rfl⟩ := ODmk.surjective u
  obtain ⟨b, rfl⟩ := ODmk.surjective v
  rw [← map_add, ODtaylorCoeff_mk, ODtaylorCoeff_mk, ODtaylorCoeff_mk]
  exact Weierstrass.taylorCoeff_add (analyticAt_zero_of_mem_diskAnalytic a.2)
    (analyticAt_zero_of_mem_diskAnalytic b.2)

theorem ODtaylorCoeff_mul (u v : OD) (n : ℕ) :
    ODtaylorCoeff (u * v) n =
      ∑ i ∈ Finset.range (n + 1), ODtaylorCoeff u i * ODtaylorCoeff v (n - i) := by
  obtain ⟨a, rfl⟩ := ODmk.surjective u
  obtain ⟨b, rfl⟩ := ODmk.surjective v
  rw [← map_mul, ODtaylorCoeff_mk]
  simp only [ODtaylorCoeff_mk]
  exact taylorCoeff_mul_eq (analyticAt_zero_of_mem_diskAnalytic a.2)
    (analyticAt_zero_of_mem_diskAnalytic b.2) n

theorem ODtaylorCoeff_one (n : ℕ) :
    ODtaylorCoeff (1 : OD) n = if n = 0 then 1 else 0 := by
  show ODtaylorCoeff (ODmk 1) n = _
  rw [ODtaylorCoeff_mk]
  exact taylorCoeff_one n

theorem ODtaylorCoeff_zero (n : ℕ) : ODtaylorCoeff (0 : OD) n = 0 := by
  show ODtaylorCoeff (ODmk 0) n = _
  rw [ODtaylorCoeff_mk]
  show taylorCoeff (fun _ : ℂ => (0 : ℂ)) n = 0
  simp [Weierstrass.taylorCoeff]

/-! ## Integer coefficients of `ℛ_ℝ` -/

theorem exists_intCoeff (x : RRsub) (n : ℕ) :
    ∃ k : ℤ, (k : ℂ) = ODtaylorCoeff (RRsub.subtype x) n := by
  obtain ⟨f, hfi, hfx⟩ := mem_RRsub.mp x.2
  obtain ⟨k, hk⟩ := hfi n
  refine ⟨k, ?_⟩
  have : RRsub.subtype x = ODmk f := hfx.symm
  rw [this, ODtaylorCoeff_mk]
  simpa using hk

/-- The integer `n`-th Taylor coefficient of an element of `ℛ_ℝ`. -/
noncomputable def intCoeff (x : RRsub) (n : ℕ) : ℤ :=
  Classical.choose (exists_intCoeff x n)

theorem intCoeff_spec (x : RRsub) (n : ℕ) :
    (intCoeff x n : ℂ) = ODtaylorCoeff (RRsub.subtype x) n :=
  Classical.choose_spec (exists_intCoeff x n)

theorem intCoeff_injective_aux {x : RRsub} (h : ∀ n, intCoeff x n = 0) :
    ∀ n, ODtaylorCoeff (RRsub.subtype x) n = 0 := by
  intro n
  have := intCoeff_spec x n
  rw [h n] at this
  simpa using this.symm

/-! ## The coefficient ring homomorphism -/

/-- **The coefficient homomorphism** `ℛ_ℝ → ℤ⟦z⟧`, sending an element to the
formal power series of its (integer) Taylor coefficients. -/
noncomputable def coeffHom : RRsub →+* PowerSeries ℤ where
  toFun x := PowerSeries.mk (intCoeff x)
  map_one' := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    have : (intCoeff (1 : RRsub) n : ℂ) = if n = 0 then 1 else 0 := by
      rw [intCoeff_spec]
      have : RRsub.subtype (1 : RRsub) = (1 : OD) := map_one _
      rw [this, ODtaylorCoeff_one]
    rcases eq_or_ne n 0 with h | h <;> simp [h] at this ⊢ <;> exact_mod_cast this
  map_mul' x y := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    have key : (intCoeff (x * y) n : ℂ) =
        ((∑ p ∈ Finset.antidiagonal n, intCoeff x p.1 * intCoeff y p.2 : ℤ) : ℂ) := by
      rw [intCoeff_spec]
      have hsub : RRsub.subtype (x * y) = RRsub.subtype x * RRsub.subtype y := map_mul _ _ _
      rw [hsub, ODtaylorCoeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      push_cast
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [intCoeff_spec, intCoeff_spec]
    exact_mod_cast key
  map_zero' := by
    ext n
    simp only [PowerSeries.coeff_mk, map_zero]
    have : (intCoeff (0 : RRsub) n : ℂ) = 0 := by
      rw [intCoeff_spec]
      have : RRsub.subtype (0 : RRsub) = (0 : OD) := map_zero _
      rw [this, ODtaylorCoeff_zero]
    exact_mod_cast this
  map_add' x y := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]
    have : (intCoeff (x + y) n : ℂ) = (intCoeff x n : ℂ) + (intCoeff y n : ℂ) := by
      rw [intCoeff_spec]
      have hsub : RRsub.subtype (x + y) = RRsub.subtype x + RRsub.subtype y :=
        map_add RRsub.subtype x y
      rw [hsub, ODtaylorCoeff_add, intCoeff_spec, intCoeff_spec]
    exact_mod_cast this

@[simp] theorem coeff_coeffHom (x : RRsub) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (coeffHom x) = intCoeff x n := by
  simp [coeffHom]

end RequestProject
