import RequestProject.Main

/-!
# Convergence estimates (Section "Proofs", Step 3)

This file formalizes the analytic estimates underlying Step 3 of the proof of
Theorem (Gaussian-integer realization) in the paper *Integer Coefficients Power
Series with Prescribed Zero Sets* by Bannon–Feldman.

The key quantitative facts are:

* `Gtail_summable` : the tail series `∑_{k ≥ n+2} w^k/k` converges for `‖w‖ < 1`.
* `Gtail_norm_le` : `‖∑_{k ≥ n+2} w^k/k‖ ≤ ρ^(n+2)/(1-ρ)` when `‖w‖ ≤ ρ < 1`.
* `G_norm_le` : the Step 3 bound
  `‖G n c w‖ ≤ ‖c-1‖/(n+1) · ρ^(n+1) + ρ^(n+2)/(1-ρ)` for `‖w‖ ≤ ρ < 1`.
* `E_sub_one_norm_le` : `‖E n c w - 1‖ ≤ 2 ‖G n c w‖` for `‖w‖ < 1` with
  `‖G n c w‖ ≤ 1`, the comparison used to invoke the infinite-product criterion.
-/

open scoped BigOperators

namespace RequestProject

open Complex

/-
The tail series defining `Gtail` is summable on the open unit disk.
-/
lemma Gtail_summable (n : ℕ) (w : ℂ) (hw : ‖w‖ < 1) :
    Summable (fun k : ℕ => w ^ (k + (n + 2)) / ((k : ℂ) + (n + 2))) := by
  have h_geo_series : Summable (fun k : ℕ => ‖w‖^(k + (n + 2))) := by
    exact Summable.comp_injective ( summable_geometric_of_lt_one ( norm_nonneg _ ) hw ) ( add_left_injective _ );
  refine' .of_norm _;
  exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun _ => by simpa using div_le_self ( by positivity ) ( mod_cast by linarith ) ) h_geo_series

/-
Norm bound for the tail series on a closed subdisk: for `‖w‖ ≤ ρ < 1`,
`‖Gtail n w‖ ≤ ρ^(n+2)/(1-ρ)`.
-/
lemma Gtail_norm_le (n : ℕ) (w : ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hw : ‖w‖ ≤ ρ) :
    ‖Gtail n w‖ ≤ ρ ^ (n + 2) / (1 - ρ) := by
  by_cases hw0 : w = 0;
  · simp_all +decide [ Gtail ];
    exact div_nonneg ( pow_nonneg hρ0 _ ) ( sub_nonneg.2 hρ1.le );
  · refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
    · norm_num [ pow_add ];
      exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun i => by exact div_le_self ( by positivity ) ( by norm_cast; linarith ) ) ( Summable.mul_right _ <| summable_geometric_of_lt_one ( by positivity ) <| show ‖w‖ < 1 by linarith );
    · refine' le_trans ( Summable.tsum_le_tsum _ _ _ ) _;
      use fun i => ρ ^ ( i + ( n + 2 ) );
      · norm_num;
        exact fun i => le_trans ( div_le_self ( by positivity ) ( by norm_cast; linarith ) ) ( pow_le_pow_left₀ ( by positivity ) hw _ );
      · norm_num +zetaDelta at *;
        exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun i => by exact div_le_self ( by positivity ) ( by norm_cast; linarith ) ) ( Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( show ‖w‖ < 1 by linarith ) ) ( by intros a b; aesop ) );
      · exact Summable.comp_injective ( summable_geometric_of_lt_one hρ0 hρ1 ) ( add_left_injective _ );
      · ring_nf;
        rw [ tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1 ] ; ring_nf ; norm_num

/-
**The Step 3 bound on `G`.** For `‖w‖ ≤ ρ < 1`,
`‖G n c w‖ ≤ ‖c-1‖/(n+1) · ρ^(n+1) + ρ^(n+2)/(1-ρ)`.
-/
lemma G_norm_le (n : ℕ) (c w : ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hw : ‖w‖ ≤ ρ) :
    ‖G n c w‖ ≤ ‖c - 1‖ / ((n : ℝ) + 1) * ρ ^ (n + 1) + ρ ^ (n + 2) / (1 - ρ) := by
  convert norm_sub_le ( ( c - 1 ) * w ^ ( n + 1 ) / ( n + 1 ) ) ( Gtail n w ) |> le_trans <| add_le_add ?_ ?_ using 1;
  · norm_num [ div_mul_eq_mul_div ];
    gcongr ; norm_cast;
  · exact Gtail_norm_le n w ρ hρ0 hρ1 hw

/-
**Comparison of `E - 1` with `G`.** On the open unit disk, when
`‖G n c w‖ ≤ 1`, one has `‖E n c w - 1‖ ≤ 2 ‖G n c w‖`.  This is the bound that
feeds the standard infinite-product convergence criterion.
-/
lemma E_sub_one_norm_le (n : ℕ) (c w : ℂ) (hw : ‖w‖ < 1)
    (hG : ‖G n c w‖ ≤ 1) :
    ‖E n c w - 1‖ ≤ 2 * ‖G n c w‖ := by
  convert norm_exp_sub_one_le hG using 1;
  rw [ E_eq_exp_G n c w hw ]

end RequestProject