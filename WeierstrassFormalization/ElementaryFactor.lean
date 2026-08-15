/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Basic

/-!
# Modified elementary factors

Formalizes Section 2 of Bannon–Feldman, *Integer Coefficients Power Series with
Prescribed Zero Sets*: the **modified elementary factor**
`E n c w = (1 - w) * exp (∑_{k=1}^n w^k/k + c * w^(n+1)/(n+1))`
and its structural lemma.

We also introduce the Taylor-coefficient operator `taylorCoeff f m = [z^m] f`
(the `m`-th coefficient of the power series of `f` at `0`) with its basic calculus,
and the exponent `G` for which `E n c w = exp (G n c w)` on the disk.
-/

open Complex

namespace Weierstrass

/-- The exponent appearing in the modified elementary factor:
`H n c w = ∑_{k=1}^n w^k/k + c * w^(n+1)/(n+1)`. -/
noncomputable def H (n : ℕ) (c w : ℂ) : ℂ :=
  (∑ k ∈ Finset.Icc 1 n, w ^ k / (k : ℂ)) + c * w ^ (n + 1) / ((n : ℂ) + 1)

/-- The **modified elementary factor** of order `n` with parameter `c`:
`E n c w = (1 - w) * exp (H n c w)`. For `c = 1` this is the classical
Weierstrass factor. (Written out inline so that `fun_prop` sees the elementary
components.) -/
noncomputable def E (n : ℕ) (c w : ℂ) : ℂ :=
  (1 - w) * Complex.exp ((∑ k ∈ Finset.Icc 1 n, w ^ k / (k : ℂ))
    + c * w ^ (n + 1) / ((n : ℂ) + 1))

/-- `E` written in terms of the exponent `H`. -/
theorem E_eq_H (n : ℕ) (c w : ℂ) : E n c w = (1 - w) * Complex.exp (H n c w) := rfl

/-- The exponent `G` from the structural lemma:
`G n c w = (c-1) w^(n+1)/(n+1) - ∑_{k ≥ n+2} w^k/k`. -/
noncomputable def G (n : ℕ) (c w : ℂ) : ℂ :=
  (c - 1) * w ^ (n + 1) / ((n : ℂ) + 1) - ∑' k : ℕ, if k ≥ n + 2 then w ^ k / (k : ℂ) else 0

/-- The `m`-th Taylor coefficient of `f` at `0`, i.e. `[z^m] f` for `f` analytic
at `0`. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (m : ℕ) : ℂ :=
  iteratedDeriv m f 0 / (m.factorial : ℂ)

/-! ## Basic values and the exponential identity -/

/-- Part (i): `E n c 0 = 1`. -/
theorem E_zero (n : ℕ) (c : ℂ) : E n c 0 = 1 := by
  simp only [E]
  rw [Finset.sum_eq_zero] <;> aesop

/-- Part (iv)/(v): over all of `ℂ`, the only zero of `E n c` is the simple zero at
`w = 1`. -/
theorem E_zero_iff (n : ℕ) (c w : ℂ) : E n c w = 0 ↔ w = 1 := by
  simp only [E, mul_eq_zero, Complex.exp_ne_zero, or_false, sub_eq_zero]
  rw [eq_comm]

/-
The central identity (eq. (Eexp)–(Gdef)): on the open unit disk,
`E n c w = exp (G n c w)`.
-/
theorem E_eq_exp_G {n : ℕ} {c w : ℂ} (hw : w ∈ 𝔻) :
    E n c w = Complex.exp (G n c w) := by
  have := @Complex.hasSum_taylorSeries_neg_log w ; simp_all +decide;
  have hG : G n c w = (∑ k ∈ Finset.Icc 1 n, w ^ k / (k : ℂ)) + c * w ^ (n + 1) / ((n : ℂ) + 1) + Complex.log (1 - w) := by
    have hG : ∑' k : ℕ, (if k ≥ n + 2 then w ^ k / (k : ℂ) else 0) = (∑' k : ℕ, w ^ k / (k : ℂ)) - (∑ k ∈ Finset.range (n + 2), w ^ k / (k : ℂ)) := by
      rw [ ← Summable.sum_add_tsum_nat_add ( n + 2 ) this.summable ];
      rw [ ← Summable.sum_add_tsum_nat_add ( n + 2 ) ];
      · rw [ Finset.sum_eq_zero ] <;> aesop;
      · exact Summable.of_norm <| by simpa using this.summable.norm.of_nonneg_of_le ( fun n => by positivity ) fun n => by split_ifs <;> norm_num ; positivity;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ ] at *;
    unfold G; rw [ hG, this.tsum_eq ] ; ring;
  rw [ E_eq_H, hG, Complex.exp_add ];
  rw [ Complex.exp_log ( sub_ne_zero_of_ne <| by aesop ) ] ; ring!

/-
Parts (ii)–(iii): the **triangular coefficient structure** of the modified
factor. Near `0` one has `E n c w = 1 + w^(n+1) · Φ w`, with `Φ` analytic at `0`
and `Φ 0 = (c-1)/(n+1)`.
-/
theorem E_expansion (n : ℕ) (c : ℂ) :
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧ Φ 0 = (c - 1) / ((n : ℂ) + 1) ∧
      ∀ᶠ w in nhds (0 : ℂ), E n c w = 1 + w ^ (n + 1) * Φ w := by
  -- Set `g w = (c-1)/((n:ℂ)+1) - w * ψ w`. Then `g` is analytic at `0`, `g 0 = (c-1)/((n:ℂ)+1)`, and near `0`, `G n c w = (c-1)w^(n+1)/(n+1) - w^(n+2) ψ w = w^(n+1) * ((c-1)/(n+1) - w ψ w) = w^(n+1) * g w`.
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = (c - 1) / (n + 1) ∧ ∀ᶠ w in nhds 0, G n c w = w ^ (n + 1) * g w := by
    -- The tail $\sum' k, if k ≥ n+2 then w^k/(k:ℂ) else 0$ equals $w^{n+2} * ψ w$ near $0$, where $ψ w = \sum' j : ℕ, w^j/((j:ℂ)+(n+2))$ is analytic at $0$.
    have h_tail : ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ ∀ᶠ w in nhds 0, (∑' k : ℕ, if k ≥ n + 2 then w ^ k / (k : ℂ) else 0) = w ^ (n + 2) * ψ w := by
      refine' ⟨ fun w => ∑' k : ℕ, w ^ k / ( k + n + 2 : ℂ ), _, _ ⟩;
      · refine' ( HasFPowerSeriesAt.analyticAt _ );
        exact FormalMultilinearSeries.ofScalars ℂ ( fun k => ( k + n + 2 : ℂ ) ⁻¹ );
        rw [ hasFPowerSeriesAt_iff ];
        filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with z hz;
        simp +decide [ div_eq_mul_inv ];
        refine' Summable.hasSum _;
        norm_num +zetaDelta at *;
        -- Since $|z| < 1$, the series $\sum_{k=0}^{\infty} \frac{z^k}{k+n+2}$ converges absolutely.
        have h_abs_conv : Summable (fun k : ℕ => ‖z ^ k / (k + n + 2 : ℂ)‖) := by
          norm_num [ Complex.norm_exp ];
          exact Summable.of_nonneg_of_le ( fun k => div_nonneg ( pow_nonneg ( norm_nonneg _ ) _ ) ( norm_nonneg _ ) ) ( fun k => div_le_self ( pow_nonneg ( norm_nonneg _ ) _ ) ( by norm_cast; linarith ) ) ( summable_geometric_of_lt_one ( norm_nonneg _ ) hz );
        exact .of_norm h_abs_conv;
      · filter_upwards [ Metric.ball_mem_nhds 0 zero_lt_one ] with w hw;
        rw [ ← tsum_mul_left ] ; rw [ ← Summable.sum_add_tsum_nat_add ( n + 2 ) ] ; norm_num [ add_assoc, pow_add ] ; ring_nf;
        · rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ add_comm, add_left_comm ];
        · rw [ ← summable_nat_add_iff ( n + 2 ) ];
          norm_num +zetaDelta at *;
          exact Summable.of_norm <| by simpa using Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun _ => by exact div_le_self ( by positivity ) <| mod_cast by linarith ) <| summable_nat_add_iff ( n + 2 ) |>.2 <| summable_geometric_of_lt_one ( by positivity ) hw;
    obtain ⟨ ψ, hψ₁, hψ₂ ⟩ := h_tail; use fun w => ( c - 1 ) / ( n + 1 ) - w * ψ w; simp_all +decide [ G ] ;
    exact ⟨ AnalyticAt.sub ( analyticAt_const ) ( AnalyticAt.mul ( analyticAt_id ) hψ₁ ), by filter_upwards [ hψ₂ ] with w hw; rw [ hw ] ; ring ⟩;
  -- Now set `Φ w = g w * h (w^(n+1) * g w)`. It is analytic at `0` (composition/product of analytic functions), and `Φ 0 = g 0 * h 0 = (c-1)/((n:ℂ)+1)`.
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 1 ∧ ∀ᶠ w in nhds 0, Complex.exp w - 1 = w * h w := by
    -- Define `h` as the series `∑' j : ℕ, w^j / (j + 1)!`.
    use fun w => ∑' j : ℕ, w^j / (Nat.factorial (j + 1));
    constructor;
    · refine' ( HasFPowerSeriesAt.analyticAt _ );
      exact ( FormalMultilinearSeries.ofScalars ℂ fun j => ( j + 1 |> Nat.factorial : ℂ ) ⁻¹ );
      rw [ hasFPowerSeriesAt_iff ];
      filter_upwards [ Metric.ball_mem_nhds _ zero_lt_one ] with z hz;
      simp +decide [ div_eq_mul_inv ];
      refine' Summable.hasSum _;
      field_simp;
      exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial _ |> Summable.of_nonneg_of_le ( fun n => by positivity ) fun n => by simpa using by gcongr ; linarith;
    · simp_all +decide [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ];
      rw [ tsum_eq_single 0 ] <;> simp +contextual;
      rw [ Metric.eventually_nhds_iff ];
      refine' ⟨ 1, by norm_num, fun y hy => _ ⟩ ; rw [ Summable.tsum_eq_zero_add ] ; norm_num;
      · rw [ ← tsum_mul_left ] ; exact tsum_congr fun _ => by ring;
      · exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial ( Complex.normSq y |> Real.sqrt ) ;
  refine' ⟨ fun w => g w * h ( w ^ ( n + 1 ) * g w ), _, _, _ ⟩ <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · refine' hg.1.mul _;
    apply_rules [ AnalyticAt.comp, hg.1 ];
    grind +extAll;
    all_goals apply_rules [ AnalyticAt.mul, AnalyticAt.pow, analyticAt_id, analyticAt_const ];
    exact hg.1;
  · have h_exp : ∀ᶠ w in nhds 0, E n c w = Complex.exp (G n c w) := by
      filter_upwards [ Metric.ball_mem_nhds 0 zero_lt_one ] with w hw using E_eq_exp_G hw;
    filter_upwards [ h_exp, hg.2.2, hh.2.2.filter_mono ( show Filter.Tendsto ( fun w : ℂ => w ^ ( n + 1 ) * g w ) ( nhds 0 ) ( nhds 0 ) from ContinuousAt.tendsto ( by exact ContinuousAt.mul ( continuousAt_id.pow _ ) hg.1.continuousAt ) |> fun h => h.trans <| by aesop ) ] with w hw₁ hw₂ hw₃ ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ; ring;

/-! ## Taylor-coefficient calculus -/

/-- Taylor coefficients are local: functions agreeing near `0` have the same
coefficients. -/
theorem taylorCoeff_congr {m : ℕ} {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) :
    taylorCoeff f m = taylorCoeff g m := by
  unfold taylorCoeff
  rw [Filter.EventuallyEq.iteratedDeriv_eq m h]

/-- Taylor coefficients are additive on functions analytic at `0`. -/
theorem taylorCoeff_add {m : ℕ} {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    taylorCoeff (fun z => f z + g z) m = taylorCoeff f m + taylorCoeff g m := by
  unfold taylorCoeff
  convert congr_arg (fun x : ℂ => x / (m.factorial : ℂ)) (iteratedDeriv_add ?_ ?_) using 1
  · ring
  · exact hf.contDiffAt
  · exact hg.contDiffAt

/-- The coefficient of degree `m ≤ n` of `z^(n+1) · R` vanishes. -/
theorem taylorCoeff_pow_mul_lt {n m : ℕ} (hm : m ≤ n) {R : ℂ → ℂ}
    (hR : AnalyticAt ℂ R 0) :
    taylorCoeff (fun z => z ^ (n + 1) * R z) m = 0 := by
  refine div_eq_zero_iff.mpr ?_
  have h_deriv_zero : iteratedDeriv m (fun z => z ^ (n + 1) * R z) 0
      = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℂ)
          * iteratedDeriv i (fun z => z ^ (n + 1)) 0 * iteratedDeriv (m - i) R 0 := by
    have h_prod_rule : ∀ (f g : ℂ → ℂ), AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → ∀ m : ℕ,
        iteratedDeriv m (fun z => f z * g z) 0
          = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℂ)
              * iteratedDeriv i f 0 * iteratedDeriv (m - i) g 0 := by
      intros f g hf hg m
      convert iteratedDeriv_mul (show ContDiffAt ℂ m f 0 from hf.contDiffAt)
        (show ContDiffAt ℂ m g 0 from hg.contDiffAt) using 1
    exact h_prod_rule _ _ (AnalyticAt.pow analyticAt_id _) hR _
  simp_all +decide [iteratedDeriv_eq_iterate]
  exact Or.inl <| Finset.sum_eq_zero fun x hx => by
    rw [zero_pow <| Nat.sub_ne_zero_of_lt <| by linarith [Finset.mem_range.mp hx]]; ring

/-- The coefficient of degree `n+1` of `z^(n+1) · R` is `R 0`. -/
theorem taylorCoeff_pow_mul_eq (n : ℕ) {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0) :
    taylorCoeff (fun z => z ^ (n + 1) * R z) (n + 1) = R 0 := by
  have h_leibniz : iteratedDeriv (n + 1) (fun z => z ^ (n + 1) * R z) 0
      = ∑ k ∈ Finset.range (n + 2), (Nat.choose (n + 1) k : ℂ)
          * iteratedDeriv k (fun z => z ^ (n + 1)) 0 * iteratedDeriv (n + 1 - k) R 0 := by
    have h_leibniz : ∀ {f g : ℂ → ℂ} {k : ℕ}, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
        iteratedDeriv k (fun z => f z * g z) 0
          = ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℂ)
              * iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0 := by
      intros f g k hf hg
      exact iteratedDeriv_fun_mul (hf.contDiffAt) (hg.contDiffAt)
    exact h_leibniz (by fun_prop) hR
  simp_all +decide [taylorCoeff]
  rw [Finset.sum_eq_single (n + 1)] <;> simp_all +decide
  · simp +decide [Nat.descFactorial_eq_factorial_mul_choose, Nat.factorial_ne_zero, div_eq_iff]
    simpa [Nat.factorial_succ] using by ring
  · exact fun k hk₁ hk₂ => Or.inl <| Or.inr <| Or.inr <| Nat.sub_ne_zero_of_lt <|
      lt_of_le_of_ne (Nat.le_of_lt_succ hk₁) hk₂

/-! ## Taylor coefficients of the modified factor -/

/-
Part (ii): the Taylor coefficients of `E n c` of degrees `1, …, n` vanish.
-/
theorem taylorCoeff_E_eq_zero {n : ℕ} {c : ℂ} {m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ n) :
    taylorCoeff (E n c) m = 0 := by
  obtain ⟨ Φ, hΦ₁, hΦ₂, hΦ₃ ⟩ := E_expansion n c;
  rw [ taylorCoeff_congr hΦ₃ ];
  rw [ taylorCoeff_add ];
  · convert taylorCoeff_pow_mul_lt h2 hΦ₁ using 1;
    unfold taylorCoeff; norm_num [ iteratedDeriv_eq_iterate ] ;
    cases m <;> norm_num [ Function.iterate_fixed ] at *;
  · exact analyticAt_const;
  · fun_prop

/-
Part (iii): the Taylor coefficient of `E n c` of degree `n+1` is `(c-1)/(n+1)`.
-/
theorem taylorCoeff_E_succ {n : ℕ} {c : ℂ} :
    taylorCoeff (E n c) (n + 1) = (c - 1) / ((n : ℂ) + 1) := by
  obtain ⟨Φ, hΦ_analytic, hΦ_zero, hΦ⟩ := E_expansion n c;
  rw [ ← hΦ_zero, taylorCoeff_congr hΦ ];
  rw [ taylorCoeff_add, taylorCoeff_pow_mul_eq ] <;> norm_num [ hΦ_analytic ];
  · unfold taylorCoeff; norm_num [ iteratedDeriv_succ' ] ;
  · exact analyticAt_const;
  · exact AnalyticAt.mul ( by apply_rules [ AnalyticAt.pow, analyticAt_id ] ) hΦ_analytic

end Weierstrass