import RequestProject.AffineControl

/-!
# Gaussian-integer rounding (Section "Proofs", Step 1)

This file formalizes the rounding device used in Step 1 of the proof of Theorem
(Gaussian-integer realization) in the paper *Integer Coefficients Power Series
with Prescribed Zero Sets* by Bannon–Feldman.

* `exists_gaussian_int_near` : every `v ∈ ℂ` has a Gaussian integer `T` (i.e.
  `T = p + q i` with `p, q ∈ ℤ`) within distance `√2/2`, by rounding the real and
  imaginary parts independently.
* `exists_param_round` : combined with the affine coefficient control
  (`affine_coeff_top`), for a power series `h` with `h 0 = 1` and `a ≠ 0` there is
  a parameter `c` making the degree-`(n+1)` coefficient of `h · E n c (z/a)` a
  Gaussian integer, while the rounding bound `|c-1| ≤ (√2/2)(n+1)|a|^(n+1)` holds.
-/

open scoped BigOperators

namespace RequestProject

open Complex

/-
**Nearest Gaussian integer with controlled error.**
Every `v ∈ ℂ` is within `√2/2` of some Gaussian integer `p + q i`.
-/
lemma exists_gaussian_int_near (v : ℂ) :
    ∃ p q : ℤ, ‖((p : ℂ) + (q : ℂ) * Complex.I) - v‖ ≤ Real.sqrt 2 / 2 := by
  norm_num [ Complex.normSq, Complex.norm_def ];
  exact ⟨ ⌊v.re + 1 / 2⌋, ⌊v.im + 1 / 2⌋, Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ Int.floor_le ( v.re + 1 / 2 ), Int.lt_floor_add_one ( v.re + 1 / 2 ), Int.floor_le ( v.im + 1 / 2 ), Int.lt_floor_add_one ( v.im + 1 / 2 ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ⟩ ⟩

/-
**The inductive rounding step.**
For `h` analytic at `0` with `h 0 = 1` and `a ≠ 0`, there is a parameter `c`
making the degree-`(n+1)` coefficient of `h · E n c (z/a)` a Gaussian integer,
and the corresponding bound `‖c - 1‖ ≤ (√2/2)(n+1)|a|^(n+1)` holds.
-/
lemma exists_param_round (n : ℕ) (a : ℂ) (ha : a ≠ 0) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1) :
    ∃ (c : ℂ) (p q : ℤ),
      taylorCoeff (n + 1) (fun z => h z * E n c (z / a)) = (p : ℂ) + (q : ℂ) * Complex.I ∧
      ‖c - 1‖ ≤ Real.sqrt 2 / 2 * ((n : ℝ) + 1) * ‖a‖ ^ (n + 1) := by
  obtain ⟨ p, q, hpq ⟩ := exists_gaussian_int_near ( taylorCoeff ( n + 1 ) h );
  refine' ⟨ 1 + ( p + q * Complex.I - taylorCoeff ( n + 1 ) h ) * ( ( n + 1 ) * a ^ ( n + 1 ) ), p, q, _, _ ⟩;
  · convert affine_coeff_top n ( 1 + ( p + q * Complex.I - taylorCoeff ( n + 1 ) h ) * ( ( n + 1 ) * a ^ ( n + 1 ) ) ) a ha h hh hh0 using 1;
    rw [ add_div', eq_div_iff ] <;> norm_num [ ha, Nat.cast_add_one_ne_zero ];
    ring;
  · norm_num [ mul_assoc ];
    gcongr ; norm_cast

end RequestProject