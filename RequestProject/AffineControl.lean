import RequestProject.Main

/-!
# Affine coefficient control (Lemma "Affine coefficient control")

This file formalizes the second structural lemma of Section 2 of the paper
*Integer Coefficients Power Series with Prescribed Zero Sets* by Bannon–Feldman,
the **affine coefficient control** lemma.

Let `a ≠ 0`, `n ≥ 0`, and `h` a power series convergent near `0` with `h 0 = 1`.
For `F z = h z · E n c (z/a)`:

* `[z^m] F = [z^m] h` exactly, for `0 ≤ m ≤ n` (independent of `c`); and
* `[z^(n+1)] F = [z^(n+1)] h + (c-1)/((n+1) a^(n+1))`, affine in `c`.

We record Taylor coefficients via `taylorCoeff m f = (d^m f / dz^m)(0) / m!`, which
for functions analytic at `0` is the usual power-series coefficient `[z^m] f`.
-/

open scoped BigOperators

namespace RequestProject

open Complex

/-- The `m`-th Taylor coefficient of `f` at `0`, i.e. `[z^m] f` for `f` analytic
at `0`. -/
noncomputable def taylorCoeff (m : ℕ) (f : ℂ → ℂ) : ℂ :=
  iteratedDeriv m f 0 / (m.factorial : ℂ)

/-- Taylor coefficients are local: functions agreeing near `0` have the same
coefficients. -/
lemma taylorCoeff_congr (m : ℕ) {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) :
    taylorCoeff m f = taylorCoeff m g := by
  unfold taylorCoeff
  rw [Filter.EventuallyEq.iteratedDeriv_eq m h]

/-
Taylor coefficients are additive on functions analytic at `0`.
-/
lemma taylorCoeff_add (m : ℕ) {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    taylorCoeff m (fun z => f z + g z) = taylorCoeff m f + taylorCoeff m g := by
  unfold taylorCoeff;
  convert congr_arg ( fun x : ℂ => x / ( m.factorial : ℂ ) ) ( iteratedDeriv_add ?_ ?_ ) using 1;
  · ring;
  · exact hf.contDiffAt;
  · exact hg.contDiffAt

/-
The coefficient of degree `m ≤ n` of `z^(n+1) · R` vanishes.
-/
lemma taylorCoeff_pow_mul_lt (n m : ℕ) (hm : m ≤ n) (R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 0) :
    taylorCoeff m (fun z => z ^ (n + 1) * R z) = 0 := by
  refine' div_eq_zero_iff.mpr _;
  have h_deriv_zero : iteratedDeriv m (fun z => z ^ (n + 1) * R z) 0 = ∑ i ∈ Finset.range (m + 1), Nat.choose m i * iteratedDeriv i (fun z => z ^ (n + 1)) 0 * iteratedDeriv (m - i) R 0 := by
    have h_prod_rule : ∀ (f g : ℂ → ℂ), AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → ∀ m : ℕ, iteratedDeriv m (fun z => f z * g z) 0 = ∑ i ∈ Finset.range (m + 1), Nat.choose m i * iteratedDeriv i f 0 * iteratedDeriv (m - i) g 0 := by
      intros f g hf hg m;
      convert iteratedDeriv_mul ( show ContDiffAt ℂ m f 0 from hf.contDiffAt ) ( show ContDiffAt ℂ m g 0 from hg.contDiffAt ) using 1;
    exact h_prod_rule _ _ ( by exact AnalyticAt.pow ( by exact analyticAt_id ) _ ) hR _;
  simp_all +decide [ iteratedDeriv_eq_iterate ];
  exact Or.inl <| Finset.sum_eq_zero fun x hx => by rw [ zero_pow <| Nat.sub_ne_zero_of_lt <| by linarith [ Finset.mem_range.mp hx ] ] ; ring;

/-
The coefficient of degree `n+1` of `z^(n+1) · R` is `R 0`.
-/
lemma taylorCoeff_pow_mul_eq (n : ℕ) (R : ℂ → ℂ) (hR : AnalyticAt ℂ R 0) :
    taylorCoeff (n + 1) (fun z => z ^ (n + 1) * R z) = R 0 := by
  -- Apply the Leibniz rule to expand the derivative.
  have h_leibniz : iteratedDeriv (n + 1) (fun z => z ^ (n + 1) * R z) 0 = ∑ k ∈ Finset.range (n + 2), Nat.choose (n + 1) k * iteratedDeriv k (fun z => z ^ (n + 1)) 0 * iteratedDeriv (n + 1 - k) R 0 := by
    have h_leibniz : ∀ {f g : ℂ → ℂ} {k : ℕ}, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → iteratedDeriv k (fun z => f z * g z) 0 = ∑ i ∈ Finset.range (k + 1), Nat.choose k i * iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0 := by
      intros f g k hf hg;
      have h_leibniz : ∀ {f g : ℂ → ℂ} {k : ℕ}, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → iteratedDeriv k (fun z => f z * g z) 0 = ∑ i ∈ Finset.range (k + 1), Nat.choose k i * iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0 := by
        intros f g k hf hg
        have h_leibniz : ∀ {f g : ℂ → ℂ} {k : ℕ}, ContDiffAt ℂ k f 0 → ContDiffAt ℂ k g 0 → iteratedDeriv k (fun z => f z * g z) 0 = ∑ i ∈ Finset.range (k + 1), Nat.choose k i * iteratedDeriv i f 0 * iteratedDeriv (k - i) g 0 := by
          exact fun {f g} {k} a a_1 => iteratedDeriv_fun_mul a a_1
        exact h_leibniz ( hf.contDiffAt ) ( hg.contDiffAt );
      exact h_leibniz hf hg;
    exact h_leibniz ( by fun_prop ) hR;
  simp_all +decide [ taylorCoeff ];
  rw [ Finset.sum_eq_single ( n + 1 ) ] <;> simp_all +decide;
  · simp +decide [ Nat.descFactorial_eq_factorial_mul_choose, Nat.factorial_ne_zero, div_eq_iff ];
    simpa [ Nat.factorial_succ ] using by ring;
  · exact fun k hk₁ hk₂ => Or.inl <| Or.inr <| Or.inr <| Nat.sub_ne_zero_of_lt <| lt_of_le_of_ne ( Nat.le_of_lt_succ hk₁ ) hk₂

/-
**Affine coefficient control**, remainder form.
For `h` analytic at `0` with `h 0 = 1`, `a ≠ 0`, there is `R` analytic at `0`
with `R 0 = (c-1)/((n+1) a^(n+1))` and `h z · E n c (z/a) = h z + z^(n+1) · R z`
near `0`.  This encodes simultaneously parts (i) and (ii) of the lemma.
-/
lemma affine_remainder (n : ℕ) (c a : ℂ) (ha : a ≠ 0) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      R 0 = h 0 * ((c - 1) / (((n : ℂ) + 1) * a ^ (n + 1))) ∧
      ∀ᶠ z in nhds (0 : ℂ), h z * E n c (z / a) = h z + z ^ (n + 1) * R z := by
  obtain ⟨Φ, hΦ_an, hΦ0, hΦ_eq⟩ := E_expansion n c
  -- E n c (z/a) = 1 + (z/a)^(n+1) * Φ (z/a) ; pull out z^(n+1).
  refine ⟨fun z => h z * (a ^ (n + 1))⁻¹ * Φ (z / a), ?_, ?_, ?_⟩
  ·
    apply_rules [ AnalyticAt.mul, AnalyticAt.div, analyticAt_id, analyticAt_const ];
    apply_rules [ AnalyticAt.comp, hΦ_an ];
    all_goals norm_num;
    all_goals apply_rules [ AnalyticAt.div, analyticAt_id, analyticAt_const ]
  ·
    simp +decide [ hΦ0, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ]
  ·
    filter_upwards [ hΦ_eq.filter_mono ( show Filter.Tendsto ( fun z => z / a ) ( nhds 0 ) ( nhds 0 ) by simpa using tendsto_zero_iff_norm_tendsto_zero.mpr <| by simpa using tendsto_norm_zero.div_const ( ‖a‖ : ℝ ) ) ] with z hz ; simp_all +decide [ div_eq_inv_mul, mul_pow, mul_assoc ] ; ring;

/-
**Affine coefficient control (i)**: introducing the factor `E n c (z/a)`
leaves all coefficients of degree `≤ n` unchanged.
-/
lemma affine_coeff_low (n : ℕ) (c a : ℂ) (ha : a ≠ 0) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 0) {m : ℕ} (hm : m ≤ n) :
    taylorCoeff m (fun z => h z * E n c (z / a)) = taylorCoeff m h := by
  obtain ⟨ R, hR_an, hR0, hR_eq ⟩ := affine_remainder n c a ha h hh;
  convert taylorCoeff_congr m hR_eq using 1;
  rw [ taylorCoeff_add m hh ( by exact AnalyticAt.mul ( by fun_prop ) hR_an ) ] ; norm_num [ taylorCoeff_pow_mul_lt n m hm R hR_an ]

/-
**Affine coefficient control (ii)**: the coefficient of degree `n+1` is
shifted by the affine amount `(c-1)/((n+1) a^(n+1))` (using `h 0 = 1`).
-/
lemma affine_coeff_top (n : ℕ) (c a : ℂ) (ha : a ≠ 0) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1) :
    taylorCoeff (n + 1) (fun z => h z * E n c (z / a)) =
      taylorCoeff (n + 1) h + (c - 1) / (((n : ℂ) + 1) * a ^ (n + 1)) := by
  obtain ⟨ R, hR_an, hR0, hR_eq ⟩ := affine_remainder n c a ha h hh;
  rw [ taylorCoeff_congr _ hR_eq, taylorCoeff_add ] <;> norm_num [ hh, hR_an ];
  · rw [ taylorCoeff_pow_mul_eq ] <;> aesop;
  · exact AnalyticAt.mul ( by apply_rules [ AnalyticAt.pow, analyticAt_id ] ) hR_an

end RequestProject