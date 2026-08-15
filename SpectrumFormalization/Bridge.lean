import SpectrumFormalization.Ultraproduct
import WeierstrassFormalization.IntegerRealization

/-!
# The ring-model bridge: Paper I's realization theorem inside `ℛ_ℝ`

Paper I's Theorem `thm:main` (sufficiency), formalized as
`Weierstrass.integer_realization`, produces a *function* `f : ℂ → ℂ` holomorphic
on `𝔻` with integer Taylor coefficients realizing a prescribed conjugation-invariant
effective divisor. The sequel's arguments need this statement inside the **ring
model** `ℛ_ℝ = RRsub`, and in the normalized form "constant term `1`".

This file supplies that bridge:

* `integer_realization_one` — the normalized analytic statement: if the divisor
  has multiplicity `0` at the origin, the realizing function can be taken with
  `f 0 = 1`. (The engine `Weierstrass.integer_realization_of_data` already
  produces the value `1` at `0`; `Weierstrass.integer_realization` discards this
  information when it multiplies in the monomial `z ^ D.mult 0`.)
* `exists_RRsub_realization` — the ring-model statement: such a divisor is the
  zero divisor of a representative of an element `F ∈ ℛ_ℝ` with `ev₀ F = 1`.

*Caveat, as recorded in the status file.* The conjugation-invariance hypothesis is
essential and is **not** dispensable: Paper I realizes only conjugation-invariant
divisors, since a power series with real coefficients has a conjugation-invariant
zero set (`RequestProject.zeroSet_conj_invariant`). Statements in the sequel that
realize arbitrary subsets `W` of a set `Z ⊆ 𝔻` are therefore only safe for
`Z ⊆ ℝ ∩ 𝔻` (or for conjugation-invariant `W`).
-/

open Complex Weierstrass

namespace RequestProject

/-- **Normalized realization.** A conjugation-invariant effective divisor `D` on
`𝔻` with `D.mult 0 = 0` is the zero divisor of a function `f` holomorphic on `𝔻`,
with all Taylor coefficients integers, and with `f 0 = 1`. -/
theorem integer_realization_one (D : EffectiveDivisor) (hD : D.ConjInvariant)
    (h0 : D.mult 0 = 0) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧
      (∀ m : ℕ, ∃ z : ℤ, taylorCoeff f m = z) ∧
      IsZeroDivisorOf D f ∧ f 0 = 1 := by
  obtain ⟨n, a, c, ha0, hesc, hnsum, hnfin, hcbound, hint, hcount⟩ :=
    Weierstrass.exists_integer_data D hD
  obtain ⟨hholo, hcoeff, hord, hval⟩ :=
    Weierstrass.integer_realization_of_data n a c ha0 hesc hnsum hnfin hcbound hint
  refine ⟨_, hholo, hcoeff, ?_, hval⟩
  intro z hz
  rw [hord z hz]
  rcases eq_or_ne z 0 with rfl | hz0
  · have : {k | a k = (0 : ℂ)} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact ha0 k
    rw [this, h0, Set.ncard_empty]
  · exact hcount z (mem_𝔻_iff.mp hz) hz0

/-- **The ring-model bridge.** A conjugation-invariant effective divisor `D` on
`𝔻` with `D.mult 0 = 0` is realized by an element `F` of `ℛ_ℝ` with constant term
`1`: some representative `g` of `F` in `diskAnalytic` has zero divisor `D`. -/
theorem exists_RRsub_realization (D : EffectiveDivisor) (hD : D.ConjInvariant)
    (h0 : D.mult 0 = 0) :
    ∃ (F : RRsub) (g : diskAnalytic), RRsub.subtype F = ODmk g ∧ ev0RR F = 1 ∧
      IsZeroDivisorOf D (g : ℂ → ℂ) := by
  obtain ⟨f, hholo, hcoeff, hdiv, hval⟩ := integer_realization_one D hD h0
  have hint : IsIntegerCoeffs f := by
    intro m
    obtain ⟨k, hk⟩ := hcoeff m
    exact ⟨k, by simpa using hk.symm⟩
  refine ⟨⟨ODmk ⟨f, hholo⟩, ⟨⟨f, hholo⟩, hint, rfl⟩⟩, ⟨f, hholo⟩, rfl, ?_, hdiv⟩
  have : ((ev0RR ⟨ODmk ⟨f, hholo⟩, ⟨⟨f, hholo⟩, hint, rfl⟩⟩ : ℤ) : ℂ) = (1 : ℂ) := by
    rw [ev0RR_eq, intCoeff_spec]
    show ODtaylorCoeff (ODmk ⟨f, hholo⟩) 0 = 1
    rw [ODtaylorCoeff_mk, taylorCoeff_zero_eq]
    exact hval
  exact_mod_cast this

end RequestProject
