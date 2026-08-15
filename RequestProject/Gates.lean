import RequestProject.Convergence

/-!
# Infinite-product convergence to a holomorphic limit (Section "Proofs", Step 3)

This file formalizes the analytic core of the Section 3 construction in the paper
*Integer Coefficients Power Series with Prescribed Zero Sets* by Bannon–Feldman:
**Step 3 (Convergence)**.  The partial products of modified elementary factors

`P_N(z) = ∏_{n=0}^{N-1} E_n(z / a_{n+1} ; c_{n+1})`

converge locally uniformly on the open unit disk `𝔻 = ball 0 1` to a limit that is
holomorphic on `𝔻`.

We split the argument into a reusable general core and its instantiation:

* `tprod_holo_of_forall_compact` — the general principle: if each factor `F n` is
  entire and, on every compact subset of `𝔻`, the norms `‖F n − 1‖` are eventually
  dominated by a summable sequence, then the partial products `∏_{n<N} F n`
  converge locally uniformly on `𝔻` to `z ↦ ∏' n, F n z`, which is holomorphic
  on `𝔻`.

* `E_factor_bound` — the Step 3 quantitative estimate: with the parameters obeying
  the rounding bound `‖c_{n+1} − 1‖ ≤ (√2/2)(n+1)|a_{n+1}|^{n+1}` (eq. cnbound) and
  with `|a_n| → 1`, on each closed subdisk `‖z‖ ≤ r < s < 1` the factor differences
  `‖E_n(z/a_{n+1};c_{n+1}) − 1‖` are eventually bounded by the summable sequence
  `2·((√2/2) r^{n+1} + (r/s)^{n+2}/(1 − r/s))`.

* `gates_convergence` — the conclusion: local uniform convergence of the partial
  products to a holomorphic limit on `𝔻`.
-/

open scoped BigOperators Topology

namespace RequestProject

open Complex Filter

/-
**General holomorphic-limit principle.**  Let `F n` be a sequence of entire
functions such that on every compact subset `K` of the open unit disk the
differences `‖F n − 1‖` are eventually dominated (uniformly on `K`) by a summable
sequence.  Then the partial products `∏_{n < N} F n` converge locally uniformly on
`𝔻 = ball 0 1` to `z ↦ ∏' n, F n z`, and this limit is holomorphic on `𝔻`.
-/
lemma tprod_holo_of_forall_compact
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, Differentiable ℂ (F n))
    (hbound : ∀ K : Set ℂ, K ⊆ Metric.ball 0 1 → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧
        ∀ᶠ n in atTop, ∀ z ∈ K, ‖F n z - 1‖ ≤ u n) :
    TendstoLocallyUniformlyOn (fun N z => ∏ n ∈ Finset.range N, F n z)
        (fun z => ∏' n, F n z) atTop (Metric.ball (0 : ℂ) 1)
      ∧ DifferentiableOn ℂ (fun z => ∏' n, F n z) (Metric.ball (0 : ℂ) 1) := by
  refine' ⟨ _, _ ⟩;
  · -- Apply the hypothesis `hbound` to each compact subset `K` of the open unit disk.
    have h_compact : ∀ K ⊆ Metric.ball 0 1, IsCompact K → HasProdUniformlyOn F (fun z => ∏' n, F n z) K := by
      intro K hKsub hKcompact;
      obtain ⟨ u, hu, h ⟩ := hbound K hKsub hKcompact;
      convert Summable.hasProdUniformlyOn_nat_one_add hKcompact hu h _ using 1;
      · norm_num;
      · norm_num;
      · exact fun n => ContinuousOn.sub ( hF n |> Differentiable.continuous |> Continuous.continuousOn ) continuousOn_const;
    convert hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball h_compact |> HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange using 1;
  · -- First establish `HP : HasProdLocallyUniformlyOn F (fun z => ∏' n, F n z) D`.
    have hp : HasProdLocallyUniformlyOn F (fun z => ∏' n, F n z) (Metric.ball (0 : ℂ) 1) := by
      apply hasProdLocallyUniformlyOn_of_forall_compact (Metric.isOpen_ball);
      intro K hKsub hKcompact;
      obtain ⟨ u, hu, h ⟩ := hbound K hKsub hKcompact;
      convert Summable.hasProdUniformlyOn_nat_one_add hKcompact hu h _ using 1;
      · norm_num;
      · norm_num;
      · exact fun n => ContinuousOn.sub ( hF n |> Differentiable.continuous |> Continuous.continuousOn ) continuousOn_const;
    apply_rules [ hp.tendstoLocallyUniformlyOn_finsetRange.differentiableOn ];
    · refine' Filter.Eventually.of_forall fun n => _;
      fun_prop;
    · exact Metric.isOpen_ball

/-
**Step 3 quantitative bound.**  Under the rounding bound `hγ` (eq. cnbound,
reindexed so that `γ n` plays the role of `c_{n+1}` and `α n` of `a_{n+1}`) and the
hypothesis `|α n| → 1`, on a closed subdisk `‖z‖ ≤ r` with `r < s < 1` the factor
differences `‖E_n(z/α n ; γ n) − 1‖` are eventually dominated by the summable
sequence `u n = 2·((√2/2) r^{n+1} + (r/s)^{n+2}/(1 − r/s))`.
-/
lemma E_factor_bound (α γ : ℕ → ℂ) (hα_ne : ∀ n, α n ≠ 0)
    (hα_lim : Tendsto (fun n => ‖α n‖) atTop (𝓝 1))
    (hγ : ∀ n, ‖γ n - 1‖ ≤ Real.sqrt 2 / 2 * ((n : ℝ) + 1) * ‖α n‖ ^ (n + 1))
    (r s : ℝ) (hr0 : 0 ≤ r) (hrs : r < s) (hs1 : s < 1) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ n in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
        ‖E n (γ n) (z / α n) - 1‖ ≤ u n := by
  refine' ⟨ fun n => 2 * ( Real.sqrt 2 / 2 * r ^ ( n + 1 ) + ( r / s ) ^ ( n + 2 ) / ( 1 - r / s ) ), _, _ ⟩;
  · refine Summable.mul_left _ <| Summable.add ?_ ?_;
    · exact Summable.mul_left _ ( summable_geometric_of_lt_one hr0 ( by linarith ) |> Summable.comp_injective <| Nat.succ_injective );
    · exact Summable.mul_right _ ( summable_nat_add_iff 2 |>.2 <| summable_geometric_of_lt_one ( div_nonneg hr0 <| by linarith ) <| by rw [ div_lt_iff₀ ] <;> linarith );
  · -- Choose $N$ such that for all $n \geq N$, we have $s < \|α n\|$ and $\|G n (γ n) (z / α n)\| \leq 1$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, s < ‖α n‖ ∧ ∀ z : ℂ, ‖z‖ ≤ r → ‖G n (γ n) (z / α n)‖ ≤ 1 := by
      obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ n ≥ N₁, s < ‖α n‖ := by
        simpa using hα_lim.eventually ( lt_mem_nhds hs1 )
      obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ n ≥ N₂, ∀ z : ℂ, ‖z‖ ≤ r → ‖G n (γ n) (z / α n)‖ ≤ 1 := by
        -- Choose $N$ such that for all $n \geq N$, we have $\|G n (γ n) (z / α n)\| \leq 1$.
        have hG_bound : ∃ N₂, ∀ n ≥ N₂, ∀ z : ℂ, ‖z‖ ≤ r → ‖G n (γ n) (z / α n)‖ ≤ (Real.sqrt 2 / 2) * r ^ (n + 1) + (r / s) ^ (n + 2) / (1 - r / s) := by
          use N₁; intros n hn z hz; refine' le_trans ( G_norm_le n ( γ n ) ( z / α n ) ( r / ‖α n‖ ) _ _ _ ) _;
          · positivity;
          · rw [ div_lt_iff₀ ] <;> linarith [ hN₁ n hn ];
          · simpa using div_le_div_of_nonneg_right hz ( norm_nonneg _ );
          · refine' add_le_add _ _;
            · refine' le_trans ( mul_le_mul_of_nonneg_right ( div_le_div_of_nonneg_right ( hγ n ) ( by positivity ) ) ( by positivity ) ) _;
              field_simp;
              rw [ ← mul_pow, mul_div_cancel₀ _ ( norm_ne_zero_iff.mpr ( hα_ne n ) ) ];
            · gcongr <;> try linarith [ hN₁ n hn ];
              · exact pow_nonneg ( div_nonneg hr0 ( by linarith ) ) _;
              · rw [ sub_pos, div_lt_iff₀ ] <;> linarith;
        -- Since $\sqrt{2}/2 * r^{n+1} + (r/s)^{n+2}/(1-r/s)$ tends to $0$ as $n$ tends to infinity, we can choose $N₂$ such that for all $n \geq N₂$, this expression is less than $1$.
        have h_lim_zero : Filter.Tendsto (fun n => (Real.sqrt 2 / 2) * r ^ (n + 1) + (r / s) ^ (n + 2) / (1 - r / s)) Filter.atTop (nhds 0) := by
          convert Filter.Tendsto.add ( tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by positivity ) ( show r < 1 by linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 ) ) ( Filter.Tendsto.div_const ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by exact div_nonneg hr0 ( by linarith ) ) ( show r / s < 1 by rw [ div_lt_iff₀ ] <;> linarith ) |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2 ) _ ) using 2 ; ring!;
        exact Filter.eventually_atTop.mp ( h_lim_zero.eventually ( ge_mem_nhds zero_lt_one ) ) |> fun ⟨ N₂, hN₂ ⟩ ↦ ⟨ Max.max N₂ hG_bound.choose, fun n hn z hz ↦ le_trans ( hG_bound.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) z hz ) ( hN₂ n ( le_trans ( le_max_left _ _ ) hn ) ) ⟩;
      exact ⟨ Max.max N₁ N₂, fun n hn => ⟨ hN₁ n ( le_trans ( le_max_left _ _ ) hn ), hN₂ n ( le_trans ( le_max_right _ _ ) hn ) ⟩ ⟩;
    filter_upwards [ Filter.eventually_ge_atTop N ] with n hn z hz;
    refine' le_trans ( E_sub_one_norm_le n ( γ n ) ( z / α n ) _ _ ) _;
    · rw [ norm_div ] ; exact div_lt_one ( norm_pos_iff.mpr ( hα_ne n ) ) |>.2 ( by linarith [ hN n hn ] );
    · exact hN n hn |>.2 z hz;
    · refine' mul_le_mul_of_nonneg_left ( le_trans ( G_norm_le n ( γ n ) ( z / α n ) ( r / ‖α n‖ ) ( by positivity ) ( by rw [ div_lt_iff₀ ( by linarith [ hN n hn ] ) ] ; nlinarith [ hN n hn ] ) ( by
        simpa using div_le_div_of_nonneg_right hz ( norm_nonneg _ ) ) ) _ ) zero_le_two;
      refine' add_le_add _ _;
      · refine' le_trans ( mul_le_mul_of_nonneg_right ( div_le_div_of_nonneg_right ( hγ n ) ( by positivity ) ) ( by positivity ) ) _;
        field_simp;
        rw [ ← mul_pow, mul_div_cancel₀ _ ( norm_ne_zero_iff.mpr ( hα_ne n ) ) ];
      · gcongr;
        any_goals linarith [ hN n hn ];
        · exact pow_nonneg ( div_nonneg hr0 ( by linarith ) ) _;
        · rw [ sub_pos, div_lt_iff₀ ] <;> linarith

/-
**Step 3 (Convergence).**  With the parameters obeying the rounding bound and
`|α n| → 1`, the partial products `∏_{n < N} E_n(z/α n ; γ n)` converge locally
uniformly on the open unit disk to `z ↦ ∏' n, E_n(z/α n ; γ n)`, and this limit is
holomorphic on `𝔻`.
-/
theorem gates_convergence (α γ : ℕ → ℂ) (hα_ne : ∀ n, α n ≠ 0)
    (hα_lim : Tendsto (fun n => ‖α n‖) atTop (𝓝 1))
    (hγ : ∀ n, ‖γ n - 1‖ ≤ Real.sqrt 2 / 2 * ((n : ℝ) + 1) * ‖α n‖ ^ (n + 1)) :
    TendstoLocallyUniformlyOn
        (fun N z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n))
        (fun z => ∏' n, E n (γ n) (z / α n)) atTop (Metric.ball (0 : ℂ) 1)
      ∧ DifferentiableOn ℂ (fun z => ∏' n, E n (γ n) (z / α n))
          (Metric.ball (0 : ℂ) 1) := by
  apply tprod_holo_of_forall_compact;
  · exact fun n => Differentiable.comp ( RequestProject.E_differentiable n ( γ n ) ) ( differentiable_id.div_const _ );
  · intro K hK₁ hK₂;
    -- Since K is compact, it is contained in some closed ball of radius r < 1.
    obtain ⟨r, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ K ⊆ Metric.closedBall 0 r := by
      obtain ⟨r, hr₀, hr₁⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z ∈ K, ‖z‖ ≤ r := by
        by_cases hK_empty : K = ∅;
        · exact ⟨ 0, by norm_num, by norm_num, by simp +decide [ hK_empty ] ⟩;
        · obtain ⟨z₀, hz₀⟩ : ∃ z₀ ∈ K, ∀ z ∈ K, ‖z‖ ≤ ‖z₀‖ := by
            exact hK₂.exists_isMaxOn ( Set.nonempty_iff_ne_empty.mpr hK_empty ) ( continuous_norm.continuousOn );
          exact ⟨ ‖z₀‖, norm_nonneg _, by simpa using hK₁ hz₀.1, hz₀.2 ⟩;
      exact ⟨ r, hr₀, hr₁.1, fun z hz => mem_closedBall_zero_iff.mpr ( hr₁.2 z hz ) ⟩;
    obtain ⟨ u, hu₁, hu₂ ⟩ := E_factor_bound α γ hα_ne hα_lim hγ r ( ( r + 1 ) / 2 ) hr.1 ( by linarith ) ( by linarith );
    exact ⟨ u, hu₁, hu₂.mono fun n hn z hz => hn z <| by simpa using hr.2.2 hz ⟩

end RequestProject