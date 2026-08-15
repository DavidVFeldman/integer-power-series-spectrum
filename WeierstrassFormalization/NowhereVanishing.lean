/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.AssociateFactorization

/-!
# Nowhere-vanishing functions with Gaussian-integer coefficients (Proposition `prop:nv`)

Formalizes Proposition `prop:nv` of Bannon–Feldman, *Integer Coefficients Power
Series with Prescribed Zero Sets*: **given a sequence `{aₙ} ⊂ ℂ ∖ 𝔻̄` (i.e.
`‖aₙ‖ > 1`) with `‖aₙ‖ → 1`, there is a function `f` holomorphic on `𝔻` with all
Taylor coefficients in `ℤ[i]`, nowhere vanishing on `𝔻`, and with `f(0) = 1`.**

The construction is exactly that of Theorem `prop:Zi` (`gaussian_realization`): the
product `f(z) = ∏' k, Eₖ(z / a_{k+1}; c_{k+1})`, where the correction constants
`c` are chosen by `exists_coeffSeq` to round each new Taylor coefficient to a
Gaussian integer. Because each zero `aₖ` lies outside `𝔻̄`, every factor is
nonvanishing on `𝔻`, so `f` has no zeros there. The `‖aₙ‖ → 1` hypothesis is the
paper's; the construction below in fact only uses `‖aₙ‖ > 1` (which already makes
the escape set `{k | ‖aₖ‖ < s}` empty for every `s < 1`), so the limit hypothesis
is retained only to match the statement of the paper.
-/

open Complex Filter Topology

namespace Weierstrass

/-- **Proposition `prop:nv`.** For a sequence `a : ℕ → ℂ` with `‖a n‖ > 1` for all
`n` and `‖a n‖ → 1`, there is a function `f` holomorphic on `𝔻`, with all Taylor
coefficients Gaussian integers, nowhere vanishing on `𝔻`, and with `f 0 = 1`. -/
theorem nowhere_vanishing_realization (a : ℕ → ℂ) (ha : ∀ n, 1 < ‖a n‖)
    (_hlim : Filter.Tendsto (fun n => ‖a n‖) Filter.atTop (nhds 1)) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧
      (∀ m : ℕ, ∃ w : GaussianInt, taylorCoeff f m = w) ∧
      (∀ z ∈ 𝔻, f z ≠ 0) ∧ f 0 = 1 := by
  -- The zeros are nonzero.
  have ha0 : ∀ k, a k ≠ 0 := fun k h => by
    have := ha k; rw [h] at this; simp at this; linarith
  -- The correction sequence forcing Gaussian-integer coefficients.
  obtain ⟨c, hgauss, hcbound⟩ := exists_coeffSeq a ha0
  -- Escape property is trivial: no `a k` is close to `0`.
  have hesc : ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite := by
    intro s hs
    have : {k | ‖a k‖ < s} = (∅ : Set ℕ) := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_of_lt (lt_trans hs (ha k))
    rw [this]; exact Set.finite_empty
  -- The Weierstrass `M`-test.
  have hM := exists_Mtest_of_coeffSeq a c ha0 hesc hcbound
  set f : ℂ → ℂ := fun z => ∏' k, E k (c k) (z / a k) with hf_def
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · -- Holomorphy.
    exact holomorphicOn_tprod_factors (n := id) hM
  · -- Gaussian-integer coefficients.
    exact tprod_taylorCoeff_gaussian hgauss hM
  · -- Nowhere vanishing.
    intro z hz hfz
    have hne : ∃ w ∈ 𝔻, f w ≠ 0 := by
      refine ⟨0, by simp, ?_⟩
      show (∏' k, E k (c k) (0 / a k)) ≠ 0
      have : (fun k => E k (c k) ((0 : ℂ) / a k)) = fun _ => (1 : ℂ) := by
        funext k; rw [zero_div]; exact E_zero k (c k)
      rw [this, tprod_one]; norm_num
    have hord : analyticOrderNatAt f z = {k | a k = z}.ncard :=
      isZeroDivisorOf_tprod_factors ha0 hM z hz
    have hempty : {k | a k = z} = (∅ : Set ℕ) := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      have h1 : ‖z‖ < 1 := mem_𝔻_iff.mp hz
      have h2 : 1 < ‖a k‖ := ha k
      rw [hk] at h2; linarith
    rw [hempty, Set.ncard_empty] at hord
    exact analyticOrderNatAt_ne_zero_of_eq_zero
      (holomorphicOn_tprod_factors (n := id) hM) hne hz hfz hord
  · -- `f 0 = 1`.
    show (∏' k, E k (c k) (0 / a k)) = 1
    have : (fun k => E k (c k) ((0 : ℂ) / a k)) = fun _ => (1 : ℂ) := by
      funext k; rw [zero_div]; exact E_zero k (c k)
    rw [this, tprod_one]

end Weierstrass
