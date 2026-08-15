import RequestProject.AffineControl

/-!
# Conjugation symmetry and real Taylor coefficients

This file develops the conjugation-symmetry tools underlying Theorem (main) of
the paper *Integer Coefficients Power Series with Prescribed Zero Sets* by
Bannon–Feldman.

* `E_conj`: the modified elementary factor satisfies
  `conj (E n c w) = E n (conj c) (conj w)`.
* `taylorCoeff_isReal_of_conjSymm`: a holomorphic function `F` with the
  conjugation symmetry `conj (F (conj z)) = F z` has real Taylor coefficients.
* `pair_conjSymm`: the conjugate-pair product
  `E n c (z/a) · E n (conj c) (z / conj a)` is conjugation-symmetric, hence (by
  the previous lemma) has real Taylor coefficients.  This is the device that
  keeps the partial-product coefficients real in the proof of Theorem (main).
-/

open scoped BigOperators

namespace RequestProject

open Complex

/-
**Conjugation symmetry of the modified factor.**
`conj (E n c w) = E n (conj c) (conj w)`.
-/
lemma E_conj (n : ℕ) (c w : ℂ) :
    (starRingEnd ℂ) (E n c w) = E n ((starRingEnd ℂ) c) ((starRingEnd ℂ) w) := by
  simp only [E, H, map_mul, map_sub, map_one, ← Complex.exp_conj, map_add, map_sum,
    map_div₀, map_pow, map_natCast]

/-
The complex derivative interacts with the conjugation conjugacy:
`d/dz (conj ∘ F ∘ conj) (z) = conj (F' (conj z))`.
-/
lemma deriv_conj_comp {F : ℂ → ℂ} (hF : Differentiable ℂ F) (z : ℂ) :
    deriv (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) z
      = (starRingEnd ℂ) (deriv F ((starRingEnd ℂ) z)) := by
  have h_deriv : HasDerivAt (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) ((starRingEnd ℂ) (deriv F ((starRingEnd ℂ) z))) z := by
    have := hF ( starRingEnd ℂ z );
    convert this.hasDerivAt.star_conj using 1;
    norm_num;
  exact h_deriv.deriv

/-
The function `conj ∘ F ∘ conj` is again entire when `F` is.
-/
lemma differentiable_conj_comp {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) := by
  intro z
  have h_conj_diff : HasDerivAt (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) (starRingEnd ℂ (deriv F (starRingEnd ℂ z))) z := by
    rw [ hasDerivAt_iff_tendsto_slope_zero ];
    have h_diff : Filter.Tendsto (fun t => (F (starRingEnd ℂ z + t) - F (starRingEnd ℂ z)) / t) (nhdsWithin 0 {0}ᶜ) (nhds (deriv F (starRingEnd ℂ z))) := by
      simpa [ div_eq_inv_mul ] using hF.differentiableAt.hasDerivAt.tendsto_slope_zero;
    convert Complex.continuous_conj.continuousAt.tendsto.comp ( h_diff.comp ( show Filter.Tendsto ( fun t : ℂ => starRingEnd ℂ t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from ?_ ) ) using 2 ; norm_num ; ring;
    rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop
  exact h_conj_diff.differentiableAt

/-
Iterated derivatives of `conj ∘ F ∘ conj`.
-/
lemma iteratedDeriv_conj_comp (m : ℕ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) (z : ℂ) :
    iteratedDeriv m (fun z => (starRingEnd ℂ) (F ((starRingEnd ℂ) z))) z
      = (starRingEnd ℂ) (iteratedDeriv m F ((starRingEnd ℂ) z)) := by
  induction' m with m ih generalizing z <;> simp_all +decide [ iteratedDeriv_succ ];
  convert deriv_conj_comp _ _ using 1;
  · exact congr_arg ( deriv · z ) ( funext ih );
  · apply_rules [ ContDiff.differentiable_iteratedDeriv, hF.contDiff ];
    exacts [ ⊤, by norm_num ]

/-
**Real Taylor coefficients from conjugation symmetry.**
If `F` is entire and `conj (F (conj z)) = F z` for all `z`, then every Taylor
coefficient of `F` at `0` is real (fixed by conjugation).
-/
lemma taylorCoeff_isReal_of_conjSymm {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsymm : ∀ z, (starRingEnd ℂ) (F ((starRingEnd ℂ) z)) = F z) (m : ℕ) :
    (starRingEnd ℂ) (taylorCoeff m F) = taylorCoeff m F := by
  convert congr_arg ( fun x : ℂ => ( starRingEnd ℂ ) x / ( m.factorial : ℂ ) ) ( show iteratedDeriv m F 0 = ( starRingEnd ℂ ) ( iteratedDeriv m F 0 ) from ?_ ) using 1;
  · unfold taylorCoeff; norm_num [ div_eq_mul_inv ] ;
  · unfold taylorCoeff; aesop;
  · have := iteratedDeriv_conj_comp m hF;
    simpa [ hsymm ] using this 0

/-
**The conjugate-pair product is conjugation-symmetric.**
With `F z = E n c (z/a) · E n (conj c) (z / conj a)`, one has
`conj (F (conj z)) = F z`.
-/
lemma pair_conjSymm (n : ℕ) (c a z : ℂ) :
    (starRingEnd ℂ)
        (E n c ((starRingEnd ℂ) z / a) *
          E n ((starRingEnd ℂ) c) ((starRingEnd ℂ) z / (starRingEnd ℂ) a))
      = E n c (z / a) * E n ((starRingEnd ℂ) c) (z / (starRingEnd ℂ) a) := by
  by_cases ha : a = 0 <;> simp_all +decide [ E_conj ]; all_goals ring

/-
The conjugate-pair product has real Taylor coefficients.
-/
lemma pair_taylorCoeff_isReal (n : ℕ) (c a : ℂ) (m : ℕ) :
    (starRingEnd ℂ)
        (taylorCoeff m
          (fun z => E n c (z / a) * E n ((starRingEnd ℂ) c) (z / (starRingEnd ℂ) a)))
      = taylorCoeff m
          (fun z => E n c (z / a) * E n ((starRingEnd ℂ) c) (z / (starRingEnd ℂ) a)) := by
  apply taylorCoeff_isReal_of_conjSymm;
  · exact Differentiable.mul ( E_differentiable n c |> Differentiable.comp <| differentiable_id.div_const _ ) ( E_differentiable n ( starRingEnd ℂ c ) |> Differentiable.comp <| differentiable_id.div_const _ );
  · exact fun z => pair_conjSymm n c a z

end RequestProject