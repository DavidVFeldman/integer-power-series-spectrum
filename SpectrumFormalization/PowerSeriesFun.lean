import RequestProject.ConcreteFiber

/-!
# Functions defined by bounded-coefficient power series

A reusable building block for the sequel: given a coefficient sequence
`c : ℕ → ℂ` that is bounded in norm, the power series `∑ₙ cₙ zⁿ` has radius of
convergence at least `1`, hence defines a function `psFun c` holomorphic on the
open unit disk `𝔻`, whose `m`-th Taylor coefficient at `0` is exactly `cₘ` and
which sums to `∑' n, cₙ zⁿ` at each `z ∈ 𝔻`.

This is used to realize point-evaluation surjectivity (the radix expansions of
the sequel's maximality results): every element of the value field is `f(a)` for
an explicitly built bounded-coefficient series `f`.
-/

open Complex Weierstrass FormalMultilinearSeries Filter

namespace RequestProject

/-- The function defined by the power series with coefficient sequence `c`. -/
noncomputable def psFun (c : ℕ → ℂ) : ℂ → ℂ := ofScalarsSum c

/-- With bounded coefficients, the radius of convergence is at least `1`. -/
theorem psFun_radius_ge_one {c : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖c n‖ ≤ C) :
    (1 : ENNReal) ≤ (ofScalars ℂ c).radius := by
  have h1 : ((1 : NNReal) : ENNReal) ≤ (ofScalars ℂ c).radius := by
    apply le_radius_of_bound _ (max C 0)
    intro n
    have : ‖ofScalars ℂ c n‖ = ‖c n‖ := ofScalars_norm ℂ c n
    rw [this]
    simp only [NNReal.coe_one, one_pow, mul_one]
    exact le_trans (hC n) (le_max_left _ _)
  simpa using h1

/-- With bounded coefficients, `psFun c` is analytic on a neighborhood of `𝔻`. -/
theorem psFun_analyticOnNhd {c : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖c n‖ ≤ C) :
    AnalyticOnNhd ℂ (psFun c) 𝔻 := by
  have hr : (0 : ENNReal) < (ofScalars ℂ c).radius :=
    lt_of_lt_of_le (by norm_num) (psFun_radius_ge_one hC)
  have hfps : HasFPowerSeriesOnBall (psFun c) (ofScalars ℂ c) 0 (ofScalars ℂ c).radius :=
    (ofScalars ℂ c).hasFPowerSeriesOnBall hr
  intro z hz
  refine hfps.analyticOnNhd z ?_
  rw [Metric.mem_eball]
  simp only [edist_zero_right]
  calc (‖z‖₊ : ENNReal) < 1 := by
            rw [mem_𝔻_iff] at hz
            exact_mod_cast hz
        _ ≤ (ofScalars ℂ c).radius := psFun_radius_ge_one hC

/-- The `m`-th Taylor coefficient of `psFun c` is `cₘ`. -/
theorem psFun_taylorCoeff {c : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖c n‖ ≤ C) (m : ℕ) :
    taylorCoeff (psFun c) m = c m := by
  have hr : (0 : ENNReal) < (ofScalars ℂ c).radius :=
    lt_of_lt_of_le (by norm_num) (psFun_radius_ge_one hC)
  have hfps : HasFPowerSeriesOnBall (psFun c) (ofScalars ℂ c) 0 (ofScalars ℂ c).radius :=
    (ofScalars ℂ c).hasFPowerSeriesOnBall hr
  have hAt : HasFPowerSeriesAt (psFun c) (ofScalars ℂ c) 0 := ⟨_, hfps⟩
  have hana : AnalyticAt ℂ (psFun c) 0 := hAt.analyticAt
  have hAt2 : HasFPowerSeriesAt (psFun c) (ofScalars ℂ (taylorCoeff (psFun c))) 0 :=
    hana.hasFPowerSeriesAt
  have heq : ofScalars ℂ c = ofScalars ℂ (taylorCoeff (psFun c)) :=
    hAt.eq_formalMultilinearSeries hAt2
  have := ofScalars_series_injective ℂ ℂ heq
  exact (congrFun this m).symm

/-- At each `z ∈ 𝔻`, `psFun c z` is the sum of the series `∑' n, cₙ zⁿ`. -/
theorem psFun_hasSum {c : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖c n‖ ≤ C) {z : ℂ}
    (hz : z ∈ 𝔻) : HasSum (fun n => c n * z ^ n) (psFun c z) := by
  have hr : (0 : ENNReal) < (ofScalars ℂ c).radius :=
    lt_of_lt_of_le (by norm_num) (psFun_radius_ge_one hC)
  have hfps : HasFPowerSeriesOnBall (psFun c) (ofScalars ℂ c) 0 (ofScalars ℂ c).radius :=
    (ofScalars ℂ c).hasFPowerSeriesOnBall hr
  have hzmem : z ∈ Metric.eball (0 : ℂ) (ofScalars ℂ c).radius := by
    rw [Metric.mem_eball]
    simp only [edist_zero_right]
    calc (‖z‖₊ : ENNReal) < 1 := by
              rw [mem_𝔻_iff] at hz; exact_mod_cast hz
          _ ≤ (ofScalars ℂ c).radius := psFun_radius_ge_one hC
  have := hfps.hasSum hzmem
  simp only [zero_add] at this
  convert this using 1
  ext n
  rw [ofScalars_apply_eq, smul_eq_mul]

/-
**Value = Taylor sum on `𝔻`.** If `g` is analytic on a neighborhood of the
open unit disk, then at every `z ∈ 𝔻`, `g z` is the sum of its Taylor series
`∑' n, (taylorCoeff g n) zⁿ`.
-/
theorem analyticOnNhd_𝔻_hasSum {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g 𝔻) {z : ℂ}
    (hz : z ∈ 𝔻) : HasSum (fun n => taylorCoeff g n * z ^ n) (g z) := by
  refine' HasSum.congr_fun _ fun n => _;
  exact fun n => iteratedDeriv n g 0 / ( n.factorial : ℂ ) * z ^ n;
  · have := @Complex.hasSum_taylorSeries_on_ball;
    simpa [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ] using this ( hg.differentiableOn.mono ( Metric.ball_subset_ball ( show 1 ≤ 1 by norm_num ) ) ) hz;
  · rfl

end RequestProject