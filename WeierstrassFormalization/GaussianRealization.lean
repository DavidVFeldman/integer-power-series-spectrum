/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.WeierstrassProduct

/-!
# Gaussian-integer realization of effective divisors

Formalizes Theorem `prop:Zi` of Bannon–Feldman, *Integer Coefficients Power Series
with Prescribed Zero Sets*: **every effective divisor on the open unit disk `𝔻` is
the zero divisor of a holomorphic function on `𝔻` whose Taylor coefficients are all
Gaussian integers.**

The construction assembles the ingredients built in `WeierstrassProduct.lean`:
* `exists_enum_of_effectiveDivisor` enumerates the support (away from `0`) as `a : ℕ → ℂ`;
* `exists_coeffSeq` produces correction constants `c : ℕ → ℂ` forcing each newly
  introduced coefficient to a Gaussian integer, with a quantitative rounding bound;
* `exists_Mtest_of_coeffSeq` supplies the Weierstrass `M`-test;
* `holomorphicOn_tprod_factors`, `isZeroDivisorOf_tprod_factors` and
  `taylorCoeff_tprod_factors_eq_partial` control the resulting infinite product.

The zero at the origin (excluded from the enumeration) is supplied by an explicit
monomial factor `z ^ D.mult 0`.
-/

open Complex Filter Topology

namespace Weierstrass

/-! ## Analytic scaffolding -/

/-- Each partial product is analytic at `0`. -/
theorem partialProduct_analyticAt (a c : ℕ → ℂ) (N : ℕ) :
    AnalyticAt ℂ (partialProduct a c N) 0 := by
  have h : Differentiable ℂ (fun z => ∏ k ∈ Finset.range N, E k (c k) (z / a k)) := by
    unfold E; fun_prop
  exact h.analyticAt 0

/-- Freezing of a low-degree coefficient: passing from the `N`-th to the `(N+1)`-st
partial product does not change the Taylor coefficient of any degree `m ≤ N`. -/
theorem partialProduct_taylorCoeff_stable (a c : ℕ → ℂ) {m N : ℕ} (hN : m ≤ N) :
    taylorCoeff (partialProduct a c (N + 1)) m = taylorCoeff (partialProduct a c N) m := by
  rw [partialProduct_succ]
  exact taylorCoeff_mul_E_eq_of_le (partialProduct_analyticAt a c N) hN

/-- Every Taylor coefficient of a partial product of degree `> m` agrees with the
coefficient at the stage `m` where it was first fixed. -/
theorem partialProduct_taylorCoeff_eq_stage (a c : ℕ → ℂ) {m N : ℕ} (hN : m ≤ N) :
    taylorCoeff (partialProduct a c N) m = taylorCoeff (partialProduct a c m) m := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [partialProduct_taylorCoeff_stable a c hN, ih]

/-- **Gaussian-integer coefficients of the infinite product.** If every stage-`N`
coefficient of the partial products is a Gaussian integer, then so is every Taylor
coefficient of the infinite product. -/
theorem tprod_taylorCoeff_gaussian {a c : ℕ → ℂ}
    (hgauss : ∀ N, ∃ z : GaussianInt, taylorCoeff (partialProduct a c N) N = z)
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E k (c k) (z / a k) - 1‖ ≤ u k)
    (m : ℕ) :
    ∃ w : GaussianInt, taylorCoeff (fun z => ∏' k, E k (c k) (z / a k)) m = w := by
  -- the coefficient of degree `m` of the limit equals that of the `(m+2)`-nd partial product
  have hlim : taylorCoeff (fun z => ∏' k, E k (c k) (z / a k)) m
      = taylorCoeff (partialProduct a c (m + 2)) m := by
    have := taylorCoeff_tprod_factors_eq_partial (a := a) (c := c) (n := id) hM
      m (m + 1) (fun K hK => by simp only [id]; omega)
    simpa [partialProduct] using this
  -- which, by freezing, equals the stage-`m` (forced) coefficient
  rw [hlim, partialProduct_taylorCoeff_eq_stage a c (show m ≤ m + 2 by omega)]
  exact hgauss m

/-! ## Coefficients and order under a monomial factor -/

/-
Multiplying by the monomial `z ^ d` shifts Taylor coefficients: the degree-`m`
coefficient of `z ^ d * g` is the degree-`(m - d)` coefficient of `g` (and `0` if
`m < d`), for `g` analytic at `0`.
-/
theorem taylorCoeff_monomial_mul {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (d m : ℕ) :
    taylorCoeff (fun z => z ^ d * g z) m = if d ≤ m then taylorCoeff g (m - d) else 0 := by
  split_ifs with h;
  · -- By definition of $taylorCoeff$, we know that
    unfold taylorCoeff;
    -- By the properties of the derivative, we can write
    have h_deriv : iteratedDeriv m (fun z => z ^ d * g z) 0 = ∑ i ∈ Finset.range (m + 1), (Nat.choose m i : ℂ) * iteratedDeriv i (fun z => z ^ d) 0 * iteratedDeriv (m - i) g 0 := by
      convert iteratedDeriv_fun_mul ( show ContDiffAt ℂ m ( fun z => z ^ d ) 0 from ?_ ) ( show ContDiffAt ℂ m g 0 from ?_ ) using 1;
      · exact contDiffAt_id.pow _;
      · exact hg.contDiffAt;
    rw [ h_deriv, Finset.sum_eq_single d ];
    · simp +decide [ iteratedDeriv_eq_iterate, Nat.cast_choose, h ];
      simp +decide [ Nat.descFactorial_self, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Nat.factorial_ne_zero ];
    · intro i hi hi'; simp_all +decide [ iteratedDeriv_eq_iterate ] ;
      omega;
    · grind;
  · have h_deriv_zero : iteratedDeriv m (fun z => z ^ d * g z) 0 = ∑ i ∈ Finset.range (m + 1), Nat.choose m i * iteratedDeriv i (fun z => z ^ d) 0 * iteratedDeriv (m - i) g 0 := by
      convert iteratedDeriv_fun_mul ( show ContDiffAt ℂ m ( fun z => z ^ d ) 0 from ?_ ) ( show ContDiffAt ℂ m g 0 from ?_ ) using 1;
      · exact contDiffAt_id.pow _;
      · exact hg.contDiffAt;
    simp_all +decide [ taylorCoeff ];
    exact Or.inl <| Finset.sum_eq_zero fun x hx => by rw [ zero_pow <| Nat.sub_ne_zero_of_lt <| by linarith [ Finset.mem_range.mp hx ] ] ; ring;

/-- If every Taylor coefficient of `g` is a Gaussian integer, then so is every Taylor
coefficient of `z ^ d * g`. -/
theorem taylorCoeff_monomial_mul_gaussian {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (d : ℕ)
    (hg_int : ∀ m, ∃ w : GaussianInt, taylorCoeff g m = w) (m : ℕ) :
    ∃ w : GaussianInt, taylorCoeff (fun z => z ^ d * g z) m = w := by
  rw [taylorCoeff_monomial_mul hg d m]
  by_cases h : d ≤ m
  · simp only [h, if_true]; exact hg_int (m - d)
  · exact ⟨0, by simp [h]⟩

/-
The analytic order of `z ^ d * g` at a point away from `0` (where the monomial does
not vanish) equals the analytic order of `g` there.
-/
theorem analyticOrderNatAt_monomial_mul_of_ne {g : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hg : AnalyticAt ℂ g z) (d : ℕ) :
    analyticOrderNatAt (fun w => w ^ d * g w) z = analyticOrderNatAt g z := by
  -- Apply the `AnalyticAt.analyticOrderAt_eq_zero` lemma to show that `analyticOrderAt (fun w => w ^ d) z = 0`.
  have h_monomial : analyticOrderAt (fun w => w ^ d) z = 0 := by
    rw [ AnalyticAt.analyticOrderAt_eq_zero ];
    · exact pow_ne_zero _ hz;
    · fun_prop;
  convert congr_arg ENat.toNat ( analyticOrderAt_mul _ _ ) using 1;
  · aesop;
  · fun_prop;
  · assumption

/-
The analytic order of `z ^ d * g` at `0` adds `d` to the analytic order of `g`.
-/
theorem analyticOrderNatAt_monomial_mul_at_zero {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 ≠ 0) (d : ℕ) :
    analyticOrderNatAt (fun w => w ^ d * g w) 0 = d := by
  convert congr_arg ENat.toNat ( analyticOrderAt_mul _ _ ) using 1;
  · rw [ hg.analyticOrderAt_eq_zero.mpr hg0 ];
    rw [ show ( fun w : ℂ => w ^ d ) = ( id : ℂ → ℂ ) ^ d by ext; rfl, analyticOrderAt_pow analyticAt_id ] ; norm_num;
  · fun_prop;
  · assumption

/-! ## The realization theorem -/

/-
**Theorem `prop:Zi`.** Every effective divisor `D` on the open unit disk is the
zero divisor of a function `f` holomorphic on `𝔻` all of whose Taylor coefficients are
Gaussian integers.
-/
theorem gaussian_realization (D : EffectiveDivisor) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧
      (∀ m : ℕ, ∃ z : GaussianInt, taylorCoeff f m = z) ∧
      IsZeroDivisorOf D f := by
  obtain ⟨a, ha0, hmult, hesc, _⟩ := exists_enum_of_effectiveDivisor D;
  obtain ⟨c, hgauss, hcbound⟩ := exists_coeffSeq a ha0;
  -- Define `g := fun z => ∏' k, E k (c k) (z / a k)` and `d := D.mult 0`, and take `f := fun z => z ^ d * g z`.
  set g : ℂ → ℂ := fun z => ∏' k, E k (c k) (z / a k)
  set d : ℕ := D.mult 0
  set f : ℂ → ℂ := fun z => z ^ d * g z;
  refine' ⟨ f, _, _, _ ⟩;
  · have := holomorphicOn_tprod_factors ( n := id ) ( exists_Mtest_of_coeffSeq a c ha0 hesc hcbound );
    exact fun z hz => AnalyticAt.mul ( by fun_prop ) ( this z hz );
  · apply taylorCoeff_monomial_mul_gaussian;
    · have := holomorphicOn_tprod_factors ( n := id ) ( fun K hK hK' => exists_Mtest_of_coeffSeq a c ha0 hesc hcbound K hK hK' );
      exact this 0 ( by norm_num [ mem_𝔻_iff ] );
    · convert tprod_taylorCoeff_gaussian hgauss _;
      convert exists_Mtest_of_coeffSeq a c ha0 hesc hcbound using 1;
  · intro z hz;
    by_cases hz0 : z = 0;
    · rw [ hz0, analyticOrderNatAt_monomial_mul_at_zero ];
      · have := holomorphicOn_tprod_factors ( n := id ) ( fun K hK hK' => exists_Mtest_of_coeffSeq a c ha0 hesc hcbound K hK hK' );
        exact this 0 ( by simp );
      · simp +zetaDelta at *;
        simp +decide [ E_zero ];
    · rw [ hmult z hz0, analyticOrderNatAt_monomial_mul_of_ne hz0 ];
      · exact Eq.symm ( isZeroDivisorOf_tprod_factors ha0 ( exists_Mtest_of_coeffSeq a c ha0 hesc hcbound ) z hz );
      · have := holomorphicOn_tprod_factors ( n := id ) ( fun K hK hK' => exists_Mtest_of_coeffSeq a c ha0 hesc hcbound K hK hK' );
        exact this z hz

end Weierstrass