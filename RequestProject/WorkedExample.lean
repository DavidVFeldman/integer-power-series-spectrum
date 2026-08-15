import RequestProject.AffineControl

/-!
# A worked example (Section "A Worked Example")

This file formalizes the concrete computation of Section 4 of the paper
*Integer Coefficients Power Series with Prescribed Zero Sets* by Bannon–Feldman,
illustrating the inductive rounding step at the first zero `a₁ = 1/3 + i/4`.

* `E0_coeff_one` : `[z^1] E₀(z/a; 1) = 0` (the step `N = 0`, where the classical
  choice `c₁ = 1` already gives an integer coefficient).
* `E0_coeff_two` : `[z^2] E₀(z/a; 1) = -1/(2 a²)` for any `a` (with the usual
  `1/0 = 0` convention this also holds at `a = 0`, so no hypothesis is needed).
* `E0_coeff_two_at_a1` : with `a₁ = 1/3 + i/4`, `[z^2] E₀(z/a₁; 1) =
  (-504 + 1728 i)/625` (`≈ -0.806 + 2.765 i`), which is **not** a Gaussian integer.
* `a1_rounding_error` : the nearest Gaussian integer is `-1 + 3i`, and the rounding
  error has modulus `√58/25 ≈ 0.305`.
* `a1_rounding_error_le` : `√58/25 ≤ √2/2`, confirming the bound of the
  inductive claim.
-/

open scoped BigOperators

namespace RequestProject

open Complex

/-- The first zero of the worked example: `a₁ = 1/3 + i/4`. -/
noncomputable def a1 : ℂ := (1 : ℂ) / 3 + Complex.I / 4

/-
Step `N = 0`: the degree-`1` coefficient of the classical factor vanishes.
-/
lemma E0_coeff_one (a : ℂ) :
    taylorCoeff 1 (fun z => E 0 1 (z / a)) = 0 := by
  unfold taylorCoeff
  unfold E H
  norm_num [ Complex.ext_iff, pow_succ' ]

/-
The degree-`2` coefficient of the classical elementary factor `E₀(z/a; 1) =
`(1 - z/a) exp(z/a)` is `-1/(2 a²)`.
-/
lemma E0_coeff_two (a : ℂ) :
    taylorCoeff 2 (fun z => E 0 1 (z / a)) = -1 / (2 * a ^ 2) := by
  unfold taylorCoeff E
  unfold H
  norm_num [ iteratedDeriv_succ' ]
  unfold deriv
  norm_num [ fderiv_apply_one_eq_deriv ]
  ring

/-
With `a₁ = 1/3 + i/4`, the degree-`2` coefficient is `(-504 + 1728 i)/625`.
-/
lemma E0_coeff_two_at_a1 :
    taylorCoeff 2 (fun z => E 0 1 (z / a1)) = (-504 + 1728 * Complex.I) / 625 := by
  rw [show a1 = (1 / 3 + Complex.I / 4) from rfl, E0_coeff_two]
  rw [eq_div_iff (by norm_num)]
  norm_num [Complex.ext_iff, sq, Complex.div_re, Complex.div_im, Complex.normSq]

/-
The rounding error to the nearest Gaussian integer `-1 + 3i` is `√58/25`.
-/
lemma a1_rounding_error :
    ‖((-1 + 3 * Complex.I) - (-504 + 1728 * Complex.I) / 625)‖ = Real.sqrt 58 / 25 := by
  norm_num [ Complex.normSq, Complex.norm_def ]

/-
The rounding error satisfies the bound `√58/25 ≤ √2/2`.
-/
lemma a1_rounding_error_le : Real.sqrt 58 / 25 ≤ Real.sqrt 2 / 2 := by
  nlinarith [ Real.sqrt_nonneg 58, Real.sqrt_nonneg 2, Real.sq_sqrt ( show 0 ≤ 58 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ) ]

end RequestProject