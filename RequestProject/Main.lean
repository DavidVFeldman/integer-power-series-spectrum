import Mathlib

/-!
# Integer-coefficient power series with prescribed zero sets

This file formalizes the constructive engine of the paper
*Integer Coefficients Power Series with Prescribed Zero Sets*
by Jon Bannon and David Feldman, namely the **modified elementary factors**
of Section 2 ("Modified Elementary Factors") and the structural lemma about
them (Lemma "Structure of the modified factor").

For `n : ℕ` and `c : ℂ`, the modified elementary factor of order `n` with
parameter `c` is
`E n c w = (1 - w) * exp (∑_{k=1}^n w^k/k + c * w^(n+1)/(n+1))`.
For `c = 1` this is the classical Weierstrass elementary factor `E_n`.

We prove:
* `RequestProject.E_at_zero` : `E n c 0 = 1` (part (i)).
* `RequestProject.E_eq_exp_G` : on the open unit disk `‖w‖ < 1` one has
  `E n c w = exp (G n c w)`, the central identity (eq. (Eexp)–(Gdef)),
  where `G n c w = (c-1) w^(n+1)/(n+1) - ∑_{k≥n+2} w^k/k`.
* `RequestProject.E_ne_zero_of_norm_lt_one` : `E n c w ≠ 0` for `‖w‖ < 1`
  (part (iv)).
* `RequestProject.E_differentiable` : `E n c` is entire (part (v)).
* `RequestProject.E_eq_zero_iff` : over all of `ℂ`, `E n c w = 0 ↔ w = 1`,
  i.e. a simple zero at `w = 1` and no other zero (part (v)).

We also record the **necessity** direction of the main theorem: a holomorphic
function with real Taylor coefficients (equivalently `conj (f z) = f (conj z)`)
has a conjugation-invariant zero set.
-/

open scoped BigOperators

namespace RequestProject

open Complex

/-- The exponent appearing in the modified elementary factor:
`H n c w = ∑_{k=1}^n w^k/k + c * w^(n+1)/(n+1)`. -/
noncomputable def H (n : ℕ) (c w : ℂ) : ℂ :=
  (∑ k ∈ Finset.Icc 1 n, w ^ k / (k : ℂ)) + c * w ^ (n + 1) / ((n : ℂ) + 1)

/-- The **modified elementary factor** of order `n` with parameter `c`:
`E n c w = (1 - w) * exp (H n c w)`. For `c = 1` this is the classical
Weierstrass factor. -/
noncomputable def E (n : ℕ) (c w : ℂ) : ℂ :=
  (1 - w) * Complex.exp (H n c w)

/-- The tail series `∑_{k ≥ n+2} w^k / k`, reindexed to start from `0`. -/
noncomputable def Gtail (n : ℕ) (w : ℂ) : ℂ :=
  ∑' k : ℕ, w ^ (k + (n + 2)) / ((k : ℂ) + (n + 2))

/-- The exponent `G` from the structural lemma:
`G n c w = (c-1) w^(n+1)/(n+1) - ∑_{k ≥ n+2} w^k/k`. -/
noncomputable def G (n : ℕ) (c w : ℂ) : ℂ :=
  (c - 1) * w ^ (n + 1) / ((n : ℂ) + 1) - Gtail n w

/-
Part (i): `E n c 0 = 1`.
-/
lemma E_at_zero (n : ℕ) (c : ℂ) : E n c 0 = 1 := by
  -- By definition of H, we have H n c 0 = ∑ k ∈ Finset.Icc 1 n, 0^k / (k : ℂ) + c * 0^(n+1) / (n + 1).
  simp [E, H];
  rw [ Finset.sum_eq_zero ] <;> aesop

/-
The central identity (eq. (Eexp)–(Gdef)): on the open unit disk,
`E n c w = exp (G n c w)`.
-/
lemma E_eq_exp_G (n : ℕ) (c w : ℂ) (hw : ‖w‖ < 1) :
    E n c w = Complex.exp (G n c w) := by
  -- By definition of $G$, we have $G n c w = \sum_{k=1}^n \frac{w^k}{k} + \frac{c w^{n+1}}{n+1} - \log(1-w)$.
  have hG : G n c w = (∑ k ∈ Finset.Icc 1 n, w ^ k / (k : ℂ)) + c * w ^ (n + 1) / ((n : ℂ) + 1) - (-Complex.log (1 - w)) := by
    have h_split : -Complex.log (1 - w) = (∑ k ∈ Finset.range (n + 2), w ^ k / (k : ℂ)) + Gtail n w := by
      have h_split : HasSum (fun k : ℕ => w ^ k / (k : ℂ)) (-Complex.log (1 - w)) := by
        grind +suggestions;
      rw [ ← h_split.tsum_eq, ← Summable.sum_add_tsum_nat_add ];
      congr! 1;
      · exact tsum_congr fun i => by push_cast; ring;
      · exact h_split.summable;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ, h_split ];
    unfold G; ring;
  unfold E; simp +decide [ hG, Complex.exp_add, Complex.exp_log ( show ( 1 - w ) ≠ 0 from sub_ne_zero_of_ne <| by aesop ) ] ;
  unfold H; rw [ ← Complex.exp_add ] ; ring;

/-
Part (iv): `E n c w ≠ 0` for `w` in the open unit disk.
-/
lemma E_ne_zero_of_norm_lt_one (n : ℕ) (c w : ℂ) (hw : ‖w‖ < 1) :
    E n c w ≠ 0 := by
  convert Complex.exp_ne_zero (G n c w) using 1
  exact E_eq_exp_G n c w hw

/-
Part (v): `E n c` is an entire function of `w`.
-/
lemma E_differentiable (n : ℕ) (c : ℂ) : Differentiable ℂ (E n c) := by
  refine' Differentiable.mul _ ( Complex.differentiable_exp.comp _ );
  · exact differentiable_id.const_sub _;
  · refine' fun w => DifferentiableAt.add _ _; all_goals fun_prop

/-
Part (v): over all of `ℂ`, the only zero of `E n c` is the simple zero at
`w = 1`.
-/
lemma E_eq_zero_iff (n : ℕ) (c w : ℂ) : E n c w = 0 ↔ w = 1 := by
  simp +decide [ E, sub_eq_zero ];
  rw [ eq_comm ]

/-
**Necessity** of conjugation invariance. If a function `f` has real Taylor
coefficients, equivalently `conj (f z) = f (conj z)` for all `z`, then its zero
set is invariant under complex conjugation: if `f a = 0` then `f (conj a) = 0`.
-/
lemma zeroSet_conj_invariant {f : ℂ → ℂ}
    (hf : ∀ z, (starRingEnd ℂ) (f z) = f ((starRingEnd ℂ) z))
    {a : ℂ} (ha : f a = 0) : f ((starRingEnd ℂ) a) = 0 := by
  rw [ ← hf, ha, map_zero ]

/-
Parts (ii)–(iii): the **triangular coefficient structure** of the modified
factor. Near `0` one has
`E n c w = 1 + (c-1)/(n+1) · w^(n+1) + (higher order)`,
witnessed by an analytic remainder `Φ` with `Φ 0 = (c-1)/(n+1)`.

By uniqueness of the power-series expansion this encodes simultaneously:
* `[w^0] E = 1` (part (i)),
* `[w^m] E = 0` for `1 ≤ m ≤ n` (part (ii)), and
* `[w^(n+1)] E = (c-1)/(n+1)` (part (iii)).
-/
lemma E_expansion (n : ℕ) (c : ℂ) :
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧ Φ 0 = (c - 1) / ((n : ℂ) + 1) ∧
      ∀ᶠ w in nhds (0 : ℂ), E n c w = 1 + w ^ (n + 1) * Φ w := by
  -- Set Φ := g * h ∘ (w ^ (n + 1) * g).
  obtain ⟨g, hg_analytic, hg0⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = (c - 1) / ((n : ℂ) + 1) ∧ (∀ᶠ w in nhds 0, G n c w = w ^ (n + 1) * g w) := by
    -- Define $g$ as $g(w) = \frac{c-1}{n+1} - w \psi(w)$.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ∀ᶠ w in nhds 0, Gtail n w = w ^ (n + 2) * ψ w := by
      -- Define the helper function ψ from the structural lemma: ψ(w) = ∑' k : ℕ, w^k / ((k : ℂ) + (n + 2)).
      set ψ : ℂ → ℂ := fun w => ∑' k : ℕ, w ^ k / ((k : ℂ) + (n + 2));
      refine' ⟨ ψ, _, _ ⟩;
      · refine' ( HasFPowerSeriesAt.analyticAt _ );
        exact ( FormalMultilinearSeries.ofScalars ℂ fun k => 1 / ( k + ( n + 2 ) : ℂ ) );
        rw [ hasFPowerSeriesAt_iff ];
        filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with z hz;
        simp +zetaDelta at *;
        exact Summable.hasSum ( Summable.of_norm <| by simpa using Summable.of_nonneg_of_le ( fun k => by positivity ) ( fun k => by simpa using div_le_self ( by positivity ) ( mod_cast by linarith ) ) <| summable_geometric_of_lt_one ( by positivity ) hz );
      · filter_upwards [ Metric.ball_mem_nhds 0 zero_lt_one ] with w hw;
        exact Eq.symm ( by rw [ ← tsum_mul_left ] ; exact tsum_congr fun k => by ring );
    refine' ⟨ fun w => ( c - 1 ) / ( n + 1 ) - w * ψ w, _, _, _ ⟩ <;> norm_num [ hψ ];
    · exact AnalyticAt.sub ( analyticAt_const ) ( AnalyticAt.mul ( analyticAt_id ) hψ.1 );
    · filter_upwards [ hψ.2 ] with w hw ; simp_all +decide [ G, Gtail ] ; ring;
  -- Set Φ := g * h ∘ (w ^ (n + 1) * g), where h is the helper function.
  obtain ⟨h, hh_analytic, hh0⟩ : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 1 ∧ (∀ᶠ w in nhds 0, Complex.exp w - 1 = w * h w) := by
    -- Define h(w) = ∑' j:ℕ, w^j / (j+1)!.
    use fun w => ∑' j : ℕ, w^j / (Nat.factorial (j + 1));
    refine' ⟨ _, _, _ ⟩;
    · refine' ( HasFPowerSeriesAt.analyticAt _ );
      exact ( FormalMultilinearSeries.ofScalars ℂ fun j => ( ( j + 1 ).factorial : ℂ ) ⁻¹ );
      rw [ hasFPowerSeriesAt_iff ];
      simp +decide [ div_eq_mul_inv ];
      filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with z hz using Summable.hasSum <| by exact Summable.of_norm <| by simpa using Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by simpa using div_le_self ( by positivity ) ( mod_cast Nat.factorial_pos _ ) ) <| summable_geometric_of_lt_one ( by positivity ) <| show ‖z‖ < 1 from by simpa using hz;
    · norm_num [ tsum_eq_single 0, Nat.factorial_ne_zero ];
    · simp +decide [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ];
      filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with w hw;
      rw [ Summable.tsum_eq_zero_add ];
      · norm_num [ pow_succ', mul_div_assoc, tsum_mul_left ];
      · exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial ( Complex.normSq w |> Real.sqrt ) ;
  use fun w => g w * h (w ^ (n + 1) * g w);
  refine' ⟨ _, _, _ ⟩;
  · apply_rules [ AnalyticAt.mul, AnalyticAt.comp ];
    all_goals norm_num [ analyticAt_id, analyticAt_const ];
    all_goals apply_rules [ AnalyticAt.pow, AnalyticAt.mul, analyticAt_id, analyticAt_const ];
  · aesop;
  · have h_subst : ∀ᶠ w in nhds 0, Complex.exp (G n c w) = 1 + w ^ (n + 1) * g w * h (w ^ (n + 1) * g w) := by
      filter_upwards [ hg0.2, hh0.2.filter_mono ( show Filter.Tendsto ( fun w : ℂ => w ^ ( n + 1 ) * g w ) ( nhds 0 ) ( nhds 0 ) from ContinuousAt.tendsto ( by exact ContinuousAt.mul ( continuousAt_id.pow _ ) hg_analytic.continuousAt ) |> fun h => h.trans <| by aesop ) ] with w hw₁ hw₂ using by rw [ ← hw₂, hw₁ ] ; ring;
    filter_upwards [ h_subst, Metric.ball_mem_nhds 0 zero_lt_one ] with w hw hw' using by rw [ E_eq_exp_G n c w ( by simpa using hw' ) ] ; linear_combination hw;

end RequestProject