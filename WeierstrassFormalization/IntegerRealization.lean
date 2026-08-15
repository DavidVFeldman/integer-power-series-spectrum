/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.PairedEnumeration

/-!
# Integer-coefficient realization: sufficiency of Theorem `thm:main`

Formalizes the sufficiency direction of Theorem `thm:main` of Bannon–Feldman,
*Integer Coefficients Power Series with Prescribed Zero Sets*: **a conjugation-invariant
effective divisor `D` on `𝔻` is the zero divisor of a holomorphic function on `𝔻`
with all Taylor coefficients in `ℤ`.**

The construction follows the paper's direct slot-factor argument: the zeros are
enumerated so that conjugate pairs `{a, ā}` occupy a common "slot" (a single order
`s`), and the correction parameters are chosen in conjugation-symmetric pairs
`c, c̄`, so that every partial product taken over complete slots has *real* Taylor
coefficients. At each slot the (real) coefficient of the newly reachable degree is
rounded to the nearest integer. This keeps all partial-product coefficients real
integers throughout, avoiding the `g(z)·conj(g(z̄))` device (which yields only real,
not integer, coefficients).

The development is organized into:
* `exists_Mtest_general` — the Weierstrass `M`-test for factors of a general order
  function `n : ℕ → ℕ` (generalizing `exists_Mtest_of_coeffSeq`, which fixes
  `n = id`);
* `integer_realization_of_data` — the **engine**: given data `(n, a, c)` satisfying
  the `M`-test bound, an order-growth condition, and the integrality of the
  partial-product coefficients, the infinite product `∏' k, Eₖ` is holomorphic on
  `𝔻`, has integer Taylor coefficients, has the prescribed zero counts, and value
  `1` at `0`;
* `exists_integer_data` — the **construction**: from a conjugation-invariant divisor
  (with `0` excluded from the support) produce such data with the zero counts of
  `D`;
* `integer_realization` — the assembled sufficiency theorem, with the origin zero
  supplied by a monomial factor `z ^ D.mult 0`.
-/

open Complex Filter Topology

namespace Weierstrass

/-! ## The Weierstrass `M`-test for a general order function -/

/-
**Weierstrass convergence estimate for a general order function.** For factors
`E (n k) (c k) (· / a k)` with `n : ℕ → ℕ` an arbitrary order assignment, the
rounding bound `‖c k - 1‖ ≤ (√2/2)(n k + 1)‖a k‖^(n k + 1)` together with the escape
property and the summability of `k ↦ t^(n k)` (for `0 ≤ t < 1`) gives a Weierstrass
`M`-test on every compact `K ⊆ 𝔻`. This generalizes `exists_Mtest_of_coeffSeq`
(the case `n = id`).
-/
theorem exists_Mtest_general (a c : ℕ → ℂ) (n : ℕ → ℕ) (ha0 : ∀ k, a k ≠ 0)
    (hesc : ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite)
    (hnsum : ∀ t : ℝ, 0 ≤ t → t < 1 → Summable (fun k => t ^ n k))
    (hc : ∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (n k + 1) * ‖a k‖ ^ (n k + 1)) :
    ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k := by
  intro K hKsub hKcpt
  by_cases hKempty : K = ∅;
  · exact ⟨ fun _ => 0, summable_zero, by simp +decide [ hKempty ] ⟩;
  · obtain ⟨z₀, hz₀⟩ : ∃ z₀ ∈ K, ∀ z ∈ K, ‖z‖ ≤ ‖z₀‖ := by
      exact hKcpt.exists_isMaxOn ( Set.nonempty_iff_ne_empty.mpr hKempty ) ( continuous_norm.continuousOn );
    -- Set `s = (r + 1)/2`, so `r < s < 1`, `0 < s`, `0 ≤ r/s < 1`.
    obtain ⟨r, hr₀, hr₁⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ z ∈ K, ‖z‖ ≤ r := by
      exact ⟨ ‖z₀‖, norm_nonneg _, by simpa using hKsub hz₀.1, hz₀.2 ⟩;
    obtain ⟨s, hs₀, hs₁⟩ : ∃ s : ℝ, r < s ∧ s < 1 ∧ 0 < s := by
      exact ⟨ ( r + 1 ) / 2, by linarith, by linarith, by linarith ⟩
    set F := {k | ‖a k‖ < s} with hF_def
    have hF_finite : F.Finite := by
      exact hesc s hs₁.1
    set B : ℕ → ℝ := fun k => Real.sqrt 2 / 2 * r ^ (n k + 1) + (r / s) ^ (n k + 2) / (1 - r / s) with hB_def
    have hB_summable : Summable B := by
      have hB_summable : Summable (fun k => r ^ (n k + 1)) ∧ Summable (fun k => (r / s) ^ (n k + 2)) := by
        exact ⟨ by simpa only [ pow_succ' ] using Summable.mul_left _ ( hnsum r hr₀ hr₁.1 ), by simpa only [ pow_succ', pow_add ] using Summable.mul_left _ ( Summable.mul_left _ ( hnsum ( r / s ) ( div_nonneg hr₀ hs₁.2.le ) ( by rw [ div_lt_iff₀ hs₁.2 ] ; linarith ) ) ) ⟩;
      exact Summable.add ( hB_summable.1.mul_left _ ) ( hB_summable.2.div_const _ )
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, B k < 1 / 2 := by
      simpa using hB_summable.tendsto_atTop_zero.eventually ( gt_mem_nhds <| by norm_num )
    set Bad := F ∪ {k | k < N} with hBad_def
    have hBad_finite : Bad.Finite := by
      exact hF_finite.union ( Set.finite_lt_nat N )
    set M : ℕ → ℝ := fun k => if k ∈ Bad then sSup (Set.image (fun z => ‖E (n k) (c k) (z / a k) - 1‖) K) else 0 with hM_def
    have hM_summable : Summable M := by
      refine' summable_of_ne_finset_zero _;
      exacts [ hBad_finite.toFinset, fun k hk => if_neg <| by simpa using hk ]
    use fun k => M k + 2 * B k
    constructor
    ·
      exact Summable.add hM_summable ( hB_summable.mul_left 2 )
    ·
      intro k z hz
      by_cases hk : k ∈ Bad;
      · simp +zetaDelta at *;
        rw [ if_pos hk ];
        refine' le_add_of_le_of_nonneg ( le_csSup _ _ ) ( mul_nonneg zero_le_two <| add_nonneg ( mul_nonneg ( by positivity ) <| pow_nonneg hr₀ _ ) <| div_nonneg ( pow_nonneg ( div_nonneg hr₀ hs₁.2.le ) _ ) <| sub_nonneg.2 <| div_le_one_of_le₀ ( by linarith ) hs₁.2.le );
        · have h_cont : ContinuousOn (fun z => E (n k) (c k) (z / a k) - 1) K := by
            refine' ContinuousOn.sub _ continuousOn_const;
            refine' ContinuousOn.mul _ _;
            · exact ContinuousOn.sub continuousOn_const ( continuousOn_id.div_const _ );
            · fun_prop;
          exact IsCompact.bddAbove ( hKcpt.image_of_continuousOn ( h_cont.norm ) );
        · exact Set.mem_image_of_mem _ hz;
      · -- Since $k \notin Bad$, we have $s \leq \|a k\|$ and $N \leq k$.
        have hsk : s ≤ ‖a k‖ := by
          exact le_of_not_gt fun h => hk <| Or.inl h
        have hNk : N ≤ k := by
          exact le_of_not_gt fun hk' => hk <| Or.inr hk'
        set ρ := r / ‖a k‖ with hρ_def
        have hρ₀ : 0 ≤ ρ := by
          exact div_nonneg hr₀ ( norm_nonneg _ )
        have hρ₁ : ρ < 1 := by
          rw [ div_lt_iff₀ ] <;> linarith [ norm_pos_iff.mpr ( ha0 k ) ]
        have hzk : ‖z / a k‖ ≤ ρ := by
          simpa using div_le_div_of_nonneg_right ( hr₁.2 z hz ) ( norm_nonneg _ );
        have hG_bound : ‖G (n k) (c k) (z / a k)‖ ≤ B k := by
          refine' le_trans ( Weierstrass.norm_G_le ( n k ) ( c k ) ( z / a k ) hρ₀ hρ₁ hzk ) _;
          refine' add_le_add _ _;
          · refine' le_trans ( mul_le_mul_of_nonneg_right ( div_le_div_of_nonneg_right ( hc k ) ( by positivity ) ) ( by positivity ) ) _;
            field_simp;
            rw [ ← mul_pow, mul_div_cancel₀ _ ( norm_ne_zero_iff.mpr ( ha0 k ) ) ];
          · gcongr;
            · exact pow_nonneg ( div_nonneg hr₀ hs₁.2.le ) _;
            · exact sub_pos_of_lt ( by rw [ div_lt_iff₀ ] <;> linarith );
            · rw [ div_le_div_iff₀ ] <;> nlinarith [ norm_nonneg ( a k ) ];
            · exact div_le_div_of_nonneg_left ( by linarith ) ( by linarith ) ( by linarith );
        have hE_bound : ‖E (n k) (c k) (z / a k) - 1‖ ≤ 2 * ‖G (n k) (c k) (z / a k)‖ := by
          rw [ E_eq_exp_G ];
          · apply Complex.norm_exp_sub_one_le;
            exact hG_bound.trans ( le_trans ( le_of_lt ( hN k hNk ) ) ( by norm_num ) );
          · exact mem_ball_zero_iff.mpr ( lt_of_le_of_lt hzk hρ₁ );
        grind +splitImp

/-! ## The engine -/

/-- A convenient reindexing of `holomorphicOn_tprod_factors` to `n`. -/
theorem holomorphicOn_tprod_general {a c : ℕ → ℂ} {n : ℕ → ℕ}
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k) :
    HolomorphicOn (fun z => ∏' k, E (n k) (c k) (z / a k)) :=
  holomorphicOn_tprod_factors hM

/-
**The engine.** Given an order function `n`, zeros `a`, and correction
parameters `c` such that:
* `a k ≠ 0` and the escape property holds (`hesc`);
* `k ↦ t^(n k)` is summable for `0 ≤ t < 1` (`hnsum`) and each order value is
  reached only finitely late (`hnfin`);
* the rounding bound `hcbound` holds; and
* whenever a partial product includes every factor of order `≤ m`, its degree-`m`
  Taylor coefficient is an integer (`hint`);

the infinite product `f = ∏' k, E (n k) (c k) (· / a k)` is holomorphic on `𝔻`, has
integer Taylor coefficients, has analytic order `{k | a k = z}.ncard` at each
`z ∈ 𝔻`, and satisfies `f 0 = 1`.
-/
theorem integer_realization_of_data (n : ℕ → ℕ) (a c : ℕ → ℂ)
    (ha0 : ∀ k, a k ≠ 0)
    (hesc : ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite)
    (hnsum : ∀ t : ℝ, 0 ≤ t → t < 1 → Summable (fun k => t ^ n k))
    (hnfin : ∀ m, {k | n k ≤ m}.Finite)
    (hcbound : ∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (n k + 1) * ‖a k‖ ^ (n k + 1))
    (hint : ∀ m K, {j | n j ≤ m} ⊆ ↑(Finset.range K) →
      ∃ z : ℤ, taylorCoeff (fun w => ∏ j ∈ Finset.range K, E (n j) (c j) (w / a j)) m = z) :
    HolomorphicOn (fun z => ∏' k, E (n k) (c k) (z / a k)) ∧
      (∀ m : ℕ, ∃ z : ℤ, taylorCoeff (fun z => ∏' k, E (n k) (c k) (z / a k)) m = z) ∧
      (∀ z ∈ 𝔻, analyticOrderNatAt (fun w => ∏' k, E (n k) (c k) (w / a k)) z
        = {k | a k = z}.ncard) ∧
      (fun z => ∏' k, E (n k) (c k) (z / a k)) 0 = 1 := by
  refine' ⟨ _, _, _, _ ⟩;
  · exact holomorphicOn_tprod_factors ( exists_Mtest_general a c n ha0 hesc hnsum hcbound );
  · intro m;
    -- Let `K = max N 1`, so `K ≥ 1` and `K ≥ N`.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 ≤ K ∧ ∀ j ∈ {k | n k ≤ m}, j < K := by
      exact ⟨ Finset.sup ( hnfin m |> Set.Finite.toFinset ) id + 1, Nat.succ_pos _, fun j hj => Nat.lt_succ_of_le ( Finset.le_sup ( f := id ) ( by simpa using hj ) ) ⟩;
    have h_tail : ∀ K', K ≤ K' → m ≤ n K' := by
      exact fun k hk => not_lt.1 fun contra => not_le_of_gt ( hK.2 k contra.le ) hk;
    have := taylorCoeff_tprod_factors_eq_partial ( show ∀ K ⊆ Metric.ball 0 1, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧ ∀ k, ∀ z ∈ K, ‖E ( n k ) ( c k ) ( z / a k ) - 1‖ ≤ u k from Weierstrass.exists_Mtest_general a c n ha0 hesc hnsum hcbound ) m ( K - 1 ) ( fun K' hK' => h_tail K' <| by omega ) ; aesop;
  · apply isZeroDivisorOf_tprod_factors ha0 (exists_Mtest_general a c n ha0 hesc hnsum hcbound);
  · simp +decide [ E_zero ]

/-! ## The construction: rounding on the paired enumeration -/

/-- **The construction.** From a conjugation-invariant effective divisor `D`, whose
support avoids `0`, produce an order function `n`, zeros `a`, and correction
parameters `c` satisfying all the hypotheses of `integer_realization_of_data`, with
zero counts equal to the multiplicities of `D`. -/
theorem exists_integer_data (D : EffectiveDivisor) (hD : D.ConjInvariant) :
    ∃ (n : ℕ → ℕ) (a c : ℕ → ℂ),
      (∀ k, a k ≠ 0) ∧
      (∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite) ∧
      (∀ t : ℝ, 0 ≤ t → t < 1 → Summable (fun k => t ^ n k)) ∧
      (∀ m, {k | n k ≤ m}.Finite) ∧
      (∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (n k + 1) * ‖a k‖ ^ (n k + 1)) ∧
      (∀ m K, {j | n j ≤ m} ⊆ ↑(Finset.range K) →
        ∃ z : ℤ, taylorCoeff (fun w => ∏ j ∈ Finset.range K, E (n j) (c j) (w / a j)) m = z) ∧
      (∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → D.mult z = {k | a k = z}.ncard) := by
  obtain ⟨n, a, H, hesc, hcount⟩ := exists_pairedEnum D hD
  obtain ⟨hcbound, hint⟩ := exists_rounding H
  exact ⟨n, a, paramSeq n a, H.ha0, hesc, H.nsum, H.nfin, hcbound, hint, hcount⟩

/-! ## Sufficiency of the main theorem -/

/-
**Theorem `thm:main` (sufficiency).** A conjugation-invariant effective divisor
`D` on `𝔻` is the zero divisor of a holomorphic function on `𝔻` all of whose Taylor
coefficients are integers.
-/
theorem integer_realization (D : EffectiveDivisor) (hD : D.ConjInvariant) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧
      (∀ m : ℕ, ∃ z : ℤ, taylorCoeff f m = z) ∧
      IsZeroDivisorOf D f := by
  -- Let `d = D.mult 0`. First build the divisor `D'` obtained from `D` by zeroing the multiplicity at the origin:
  set d := D.mult 0 with hd_def
  set D' : EffectiveDivisor := ⟨fun z => if z = 0 then 0 else D.mult z, by
    intro z hz; specialize hz; by_cases h : z = 0 <;> simp_all +decide [ D.mult_eq_zero_of_not_mem_𝔻 ] ;, by
    exact fun K hK hK' => Set.Finite.subset ( D.finite_inter_compact K hK hK' ) fun x hx => by aesop;⟩ with hD'_def
  generalize_proofs at *;
  have := @Weierstrass.exists_integer_data D' (by
  unfold EffectiveDivisor.ConjInvariant; aesop;)
  generalize_proofs at *;
  obtain ⟨ n, a, c, ha0, hesc, hnsum, hnfin, hcbound, hcount, hD' ⟩ := this;
  -- Apply `integer_realization_of_data n a c ...` (feeding the six hypotheses) to obtain, for `g := fun z => ∏' k, E (n k) (c k) (z / a k)`, the four properties.
  obtain ⟨hg_holo, hg_int, hg_ord, hg0⟩ := Weierstrass.integer_realization_of_data n a c ha0 hesc hnsum hnfin hcbound hcount;
  refine' ⟨ fun z => z ^ d * ( ∏' k, E ( n k ) ( c k ) ( z / a k ) ), _, _, _ ⟩;
  · exact fun z hz => ( by fun_prop : AnalyticAt ℂ ( fun z => z ^ d ) z ).mul ( hg_holo z hz );
  · intro m;
    by_cases h : d ≤ m;
    · have := Weierstrass.taylorCoeff_monomial_mul ( show AnalyticAt ℂ ( fun z => ∏' k, E ( n k ) ( c k ) ( z / a k ) ) 0 from hg_holo 0 ( by simp +decide ) ) d m; aesop;
    · rw [ Weierstrass.taylorCoeff_monomial_mul ];
      · exact ⟨ 0, by rw [ if_neg h ] ; norm_num ⟩;
      · exact hg_holo 0 ( by simp +decide );
  · intro z hz
    by_cases hz0 : z = 0;
    · rw [ hz0, Weierstrass.analyticOrderNatAt_monomial_mul_at_zero ] <;> norm_num [ hg0 ];
      · exact hg_holo 0 ( by simp );
      · grind;
    · convert hg_ord z hz |> Eq.symm using 1;
      · have hcz := hD' z (mem_𝔻_iff.mp hz) hz0; simp only [hD'_def, hz0] at hcz; simpa using hcz;
      · apply Weierstrass.analyticOrderNatAt_monomial_mul_of_ne hz0 (hg_holo z hz) d

end Weierstrass