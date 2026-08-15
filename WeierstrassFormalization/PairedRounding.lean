/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.AssociateFactorization

/-!
# Conjugate-paired rounding for integer coefficients (engine of Theorem `thm:main`)

Given a flat enumeration `(n, a)` of the zeros, organized into *slots* (the level
sets of the order function `n`, each of size `1` or `2`, with conjugate pairs
`{a, ā}` sharing a slot), we construct correction parameters `paramSeq n a` by an
inductive rounding recursion. At each slot the (real) coefficient of the newly
reachable degree is rounded to the nearest integer, and paired factors receive
conjugate parameters. This keeps all partial products taken over `σ`-invariant
index sets *conjugation-symmetric*, hence with real Taylor coefficients, so the
rounding lands in `ℤ`.

The output (`exists_rounding`) is exactly the data hypotheses `hcbound` and `hint`
required by `integer_realization_of_data`.
-/

open Complex Filter Topology

namespace Weierstrass

/-- `conj (E n c w) = E n (conj c) (conj w)`. -/
theorem E_conj (n : ℕ) (c w : ℂ) :
    (starRingEnd ℂ) (E n c w) = E n ((starRingEnd ℂ) c) ((starRingEnd ℂ) w) := by
  simp only [E, map_mul, map_sub, map_one, ← Complex.exp_conj, map_add, map_sum,
    map_div₀, map_pow, map_natCast]

/-- A function is *conjugation-symmetric* if `conj (F (conj z)) = F z`. Such an `F`
(when analytic at `0`) has real Taylor coefficients. -/
def ConjSymm (F : ℂ → ℂ) : Prop := ∀ z, (starRingEnd ℂ) (F ((starRingEnd ℂ) z)) = F z

theorem ConjSymm.mul {F G : ℂ → ℂ} (hF : ConjSymm F) (hG : ConjSymm G) :
    ConjSymm (fun z => F z * G z) := by
  intro z; simp only [map_mul]; rw [hF, hG]

theorem conjSymm_one : ConjSymm (fun _ : ℂ => 1) := by intro z; simp

/-! ## The rounding recursion -/

/-- The rounding step: choose the correction parameter for a slot leader of order
`s` at the point `ak`, so that the degree-`(s+1)` coefficient of the current partial
product `P` is moved to the nearest integer (using the *real part* of the current
coefficient, which will be real at slot boundaries). For a real point (`ak.im = 0`)
a single factor performs the whole adjustment; for a conjugate pair (`ak.im ≠ 0`)
each of the two factors performs half. -/
noncomputable def roundStep (P : ℂ → ℂ) (s : ℕ) (ak : ℂ) : ℂ :=
  let v := taylorCoeff P (s + 1)
  let T : ℂ := ((round v.re : ℤ) : ℂ)
  if ak.im = 0 then 1 + (T - v) * (s + 1) * ak ^ (s + 1)
  else 1 + (T - v) * (s + 1) * ak ^ (s + 1) / 2

/-- The paired-rounding recursion. `auxState n a k = (P_k, param_{k-1})` where `P_k`
is the `k`-th partial product and `param_{k-1}` is the previous parameter (needed to
build conjugate pairs). -/
noncomputable def auxState (n : ℕ → ℕ) (a : ℕ → ℂ) : ℕ → (ℂ → ℂ) × ℂ
  | 0 => (fun _ => 1, 0)
  | (k + 1) =>
    let prev := auxState n a k
    let P := prev.1
    let pprev := prev.2
    let pk := if 1 ≤ k ∧ n (k - 1) = n k then
                (if (a (k - 1)).im = 0 then 1 else (starRingEnd ℂ) pprev)
              else roundStep P (n k) (a k)
    (fun z => P z * E (n k) pk (z / a k), pk)

/-- The chosen correction parameter at flat index `k`. -/
noncomputable def paramSeq (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ := (auxState n a (k + 1)).2

/-- The `k`-th partial product. -/
noncomputable def PPfun (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ → ℂ := (auxState n a k).1

/-- The conjugation involution swapping the two members of each conjugate-pair slot
and fixing real/lone indices. -/
noncomputable def sigmaIdx (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) : ℕ :=
  if (a k).im = 0 then k
  else if 1 ≤ k ∧ n (k - 1) = n k then k - 1 else k + 1

/-! ## Structural lemmas -/

theorem PPfun_zero (n : ℕ → ℕ) (a : ℕ → ℂ) : PPfun n a 0 = fun _ => 1 := rfl

theorem PPfun_succ (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) :
    PPfun n a (k + 1) = fun z => PPfun n a k z * E (n k) (paramSeq n a k) (z / a k) := rfl

theorem PPfun_eq_prod (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) :
    PPfun n a k = fun z => ∏ j ∈ Finset.range k, E (n j) (paramSeq n a j) (z / a j) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [PPfun_succ, ih]; funext z; rw [Finset.prod_range_succ]

theorem PPfun_analyticAt (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) :
    AnalyticAt ℂ (PPfun n a k) 0 := by
  have : Differentiable ℂ (PPfun n a k) := by
    rw [PPfun_eq_prod]; unfold E; fun_prop
  exact this.analyticAt 0

theorem PPfun_zero_val (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) : PPfun n a k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [PPfun_succ]; simp [ih, E_zero]

/-! ## Parameter value lemmas -/

/-- Parameter at a slot leader (start of a new order value). -/
theorem paramSeq_leader (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ)
    (hk : ¬ (1 ≤ k ∧ n (k - 1) = n k)) :
    paramSeq n a k = roundStep (PPfun n a k) (n k) (a k) := by
  unfold paramSeq auxState PPfun
  simp only [hk, if_false]

/-- Parameter at the second member of a conjugate-pair slot (nonreal). -/
theorem paramSeq_partner_pair (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ)
    (hk : 1 ≤ k ∧ n (k - 1) = n k) (hre : (a (k - 1)).im ≠ 0) :
    paramSeq n a k = (starRingEnd ℂ) (paramSeq n a (k - 1)) := by
  obtain ⟨hk1, hk2⟩ := hk
  unfold paramSeq
  conv_lhs => rw [auxState]
  simp only [hk1, hk2, and_self, if_true, hre, if_false]
  rw [Nat.sub_add_cancel hk1]

/-- Parameter at the second member of a real slot is `1`. -/
theorem paramSeq_partner_real (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ)
    (hk : 1 ≤ k ∧ n (k - 1) = n k) (hre : (a (k - 1)).im = 0) :
    paramSeq n a k = 1 := by
  obtain ⟨hk1, hk2⟩ := hk
  unfold paramSeq
  conv_lhs => rw [auxState]
  simp only [hk1, hk2, and_self, if_true, hre, if_true]

/-! ## The enumeration bundle -/

/-- The structural conditions on a flat enumeration `(n, a)` for the paired-rounding
construction: `n` is monotone starting at `0`, orders increase by at most one, each
order value is used at most twice, each two-element slot is a conjugate pair or a
pair of real points, and every nonreal index has a same-order neighbour (so nonreal
zeros always come paired). -/
structure PairedEnum (n : ℕ → ℕ) (a : ℕ → ℂ) : Prop where
  ha0 : ∀ k, a k ≠ 0
  mono : Monotone n
  n0 : n 0 = 0
  contig : ∀ k, n (k + 1) ≤ n k + 1
  le2 : ∀ k, n (k + 2) ≠ n k
  pair : ∀ k, n (k + 1) = n k →
    (a (k + 1) = (starRingEnd ℂ) (a k) ∧ (a k).im ≠ 0) ∨
      ((a k).im = 0 ∧ (a (k + 1)).im = 0)
  nonreal : ∀ k, (a k).im ≠ 0 → n (k + 1) = n k ∨ (1 ≤ k ∧ n (k - 1) = n k)

variable {n : ℕ → ℕ} {a : ℕ → ℂ}

/-! ## Properties of the conjugation involution -/

theorem sigmaIdx_n (H : PairedEnum n a) (k : ℕ) : n (sigmaIdx n a k) = n k := by
  by_cases hk : ( a k |> Complex.im ) = 0 <;> by_cases hk' : 1 ≤ k ∧ n ( k - 1 ) = n k <;> simp_all +decide [ sigmaIdx ];
  have := H.nonreal k hk; aesop;

theorem sigmaIdx_a (H : PairedEnum n a) (k : ℕ) :
    a (sigmaIdx n a k) = (starRingEnd ℂ) (a k) := by
  unfold sigmaIdx; by_cases hk : 1 ≤ k ∧ n ( k - 1 ) = n k <;> simp_all +decide ; (
  cases H.pair ( k - 1 ) ( by cases k <;> aesop ) <;> simp_all +decide [ Complex.ext_iff ]);
  split_ifs;
  · simp +decide [ Complex.ext_iff, ‹_› ];
  · tauto;
  · have := H.nonreal k ‹_›; simp_all +decide ;
    cases this <;> have := H.pair k <;> simp_all +decide

theorem sigmaIdx_involutive (H : PairedEnum n a) (k : ℕ) :
    sigmaIdx n a (sigmaIdx n a k) = k := by
  by_cases hk : ( a k |> Complex.im ) = 0 <;> simp_all +decide [ sigmaIdx ];
  have := H.pair k; split_ifs at * <;> simp_all +decide ;
  · have := H.pair ( k - 1 ) ; rcases k with ( _ | k ) <;> simp_all +decide ;
  · have := H.le2 ( k - 2 ) ; rcases k with ( _ | _ | k ) <;> simp_all +decide ;
  · cases H.nonreal k hk <;> simp_all +decide [ Complex.ext_iff ];
  · cases H.nonreal k hk <;> simp_all +decide

/-- `k` is a slot leader: it begins a new order value. -/
def IsLeader (n : ℕ → ℕ) (k : ℕ) : Prop := ¬ (1 ≤ k ∧ n (k - 1) = n k)

/-
The prefix `range K` is closed under `sigmaIdx` (partners of leaders in the
prefix stay in the prefix) when `K` is a leader position.
-/
theorem range_sigmaClosed_of_leader (H : PairedEnum n a) {K : ℕ} (hK : IsLeader n K) :
    ∀ j ∈ Finset.range K, sigmaIdx n a j ∈ Finset.range K := by
  intro j hj; by_cases hj' : ( a j |> Complex.im ) = 0 <;> simp_all +decide [ sigmaIdx ] ;
  split_ifs <;> simp_all +decide [ IsLeader ];
  · omega;
  · cases lt_or_eq_of_le ( Nat.succ_le_of_lt hj ) <;> simp_all +decide;
    cases H.nonreal j hj' <;> subst_vars <;> simp_all +decide

/-
A partial product over a `σ`-closed prefix on which the parameters are already
known to be conjugation-symmetric is conjugation-symmetric.
-/
theorem PPfun_conjSymm_aux (H : PairedEnum n a) {K : ℕ}
    (hK : ∀ j ∈ Finset.range K, sigmaIdx n a j ∈ Finset.range K)
    (hparam : ∀ j ∈ Finset.range K,
      paramSeq n a (sigmaIdx n a j) = (starRingEnd ℂ) (paramSeq n a j)) :
    ConjSymm (PPfun n a K) := by
  intro z
  rw [PPfun_eq_prod];
  simp +decide [ E_conj, map_prod ];
  apply Finset.prod_bij (fun j _ => sigmaIdx n a j);
  · assumption;
  · exact fun x hx y hy hxy => by have := sigmaIdx_involutive H x; have := sigmaIdx_involutive H y; aesop;
  · exact fun j hj => ⟨ sigmaIdx n a j, hK j hj, sigmaIdx_involutive H j ⟩;
  · grind +suggestions

theorem PPfun_differentiable (n : ℕ → ℕ) (a : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (PPfun n a k) := by
  rw [PPfun_eq_prod]; unfold E; fun_prop

/-
A conjugation-symmetric entire function has real Taylor coefficients.
-/
theorem conjSymm_taylorCoeff_real {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hs : ConjSymm F)
    (m : ℕ) : (taylorCoeff F m).im = 0 := by
  unfold taylorCoeff;
  -- By induction on $m$, we show that the $m$-th derivative of $F$ is conjugation-symmetric.
  have h_ind : ∀ m, ∀ z, iteratedDeriv m F (starRingEnd ℂ z) = starRingEnd ℂ (iteratedDeriv m F z) := by
    intro m;
    induction' m with m ih <;> simp_all +decide [ iteratedDeriv_succ ];
    · exact fun z => by rw [ ← hs, Complex.conj_conj ] ;
    · intro z;
      have h_deriv : HasDerivAt (iteratedDeriv m F) (deriv (iteratedDeriv m F) z) z := by
        apply hasDerivAt_deriv_iff.mpr;
        apply_rules [ ContDiff.differentiable_iteratedDeriv, hF.contDiff ];
        exacts [ ⊤, by norm_num ];
      have h_deriv_conj : HasDerivAt (fun z => starRingEnd ℂ (iteratedDeriv m F (starRingEnd ℂ z))) (starRingEnd ℂ (deriv (iteratedDeriv m F) z)) (starRingEnd ℂ z) := by
        rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
        convert Complex.continuous_conj.continuousAt.tendsto.comp ( h_deriv.comp ( show Filter.Tendsto ( fun t : ℂ => starRingEnd ℂ t ) ( 𝓝[≠] 0 ) ( 𝓝[≠] 0 ) from ?_ ) ) using 2 <;> norm_num [ ih ];
        rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
      convert HasDerivAt.deriv ( h_deriv_conj.congr_of_eventuallyEq _ ) using 1;
      filter_upwards [ ] using fun x => by simp +decide [ ih ] ;
  specialize h_ind m 0;
  norm_num [ Complex.ext_iff ] at *;
  exact Or.inl ( by linarith )

/-
**The parameter sequence is conjugation-symmetric under `sigmaIdx`.** Proved by
strong induction: the only case using the induction hypothesis is a *real leader*,
where the current coefficient is real because the partial product over the (already
`σ`-closed) prefix is conjugation-symmetric.
-/
theorem sigmaIdx_param (H : PairedEnum n a) (k : ℕ) :
    paramSeq n a (sigmaIdx n a k) = (starRingEnd ℂ) (paramSeq n a k) := by
  induction' k using Nat.strong_induction_on with k ih;
  by_cases hk : 1 ≤ k ∧ n (k - 1) = n k;
  · by_cases hre : ( a ( k - 1 ) |> Complex.im ) = 0 <;> simp_all +decide [ sigmaIdx ];
    · have := H.pair ( k - 1 ) ; rcases k with ( _ | k ) <;> simp_all +decide ;
      rw [ paramSeq_partner_real ] <;> norm_num [ hre, this ];
      exact hk;
    · split_ifs <;> simp_all +decide [ paramSeq_partner_pair ];
      have := H.pair ( k - 1 ) ; rcases k with ( _ | k ) <;> simp_all +decide ;
  · by_cases hre : (a k).im = 0;
    · -- By `paramSeq_leader`, `paramSeq n a k = roundStep (PPfun n a k) (n k) (a k)`.
      have hparam : paramSeq n a k = roundStep (PPfun n a k) (n k) (a k) := by
        exact paramSeq_leader n a k hk;
      -- By `PPfun_conjSymm_aux`, `PPfun n a k` is conjugation-symmetric.
      have hPPfun_conjSymm : ConjSymm (PPfun n a k) := by
        apply PPfun_conjSymm_aux H (range_sigmaClosed_of_leader H hk);
        exact fun j hj => ih j ( Finset.mem_range.mp hj );
      -- By `conjSymm_taylorCoeff_real`, `taylorCoeff (PPfun n a k) (n k + 1)` is real.
      have htaylor_real : (taylorCoeff (PPfun n a k) (n k + 1)).im = 0 := by
        exact conjSymm_taylorCoeff_real ( PPfun_differentiable n a k ) hPPfun_conjSymm _;
      unfold sigmaIdx roundStep at *; simp_all +decide [ Complex.ext_iff ] ;
      rw [ show ( a k ^ ( n k + 1 ) |> Complex.im ) = 0 from ?_ ] ; norm_num;
      induction' n k + 1 with n ih <;> simp_all +decide [ pow_succ' ];
    · obtain ⟨hk₁, hk₂⟩ : n (k + 1) = n k ∧ (a (k + 1)) = (starRingEnd ℂ) (a k) := by
        have := H.nonreal k hre;
        have := H.pair k; aesop;
      unfold sigmaIdx; simp +decide [ *, paramSeq_partner_pair ] ;

/-- A partial product over a `σ`-closed prefix is conjugation-symmetric, hence has
real Taylor coefficients. -/
theorem PPfun_conjSymm (H : PairedEnum n a) {K : ℕ}
    (hK : ∀ j ∈ Finset.range K, sigmaIdx n a j ∈ Finset.range K) :
    ConjSymm (PPfun n a K) :=
  PPfun_conjSymm_aux H hK (fun j _ => sigmaIdx_param H j)

/-- Taylor coefficients of the partial product at a leader position are real. -/
theorem taylorCoeff_PPfun_real (H : PairedEnum n a) {K : ℕ} (hK : IsLeader n K) (m : ℕ) :
    ((taylorCoeff (PPfun n a K) m).im = 0) :=
  conjSymm_taylorCoeff_real (PPfun_differentiable n a K)
    (PPfun_conjSymm H (range_sigmaClosed_of_leader H hK)) m

/-! ## The rounding bound and integrality -/

/-
The rounding bound at a leader position, from the explicit `roundStep` formula
and the realness of the current coefficient.
-/
theorem paramSeq_bound_leader (H : PairedEnum n a) {k : ℕ} (hk : IsLeader n k) :
    ‖paramSeq n a k - 1‖ ≤ Real.sqrt 2 / 2 * (n k + 1) * ‖a k‖ ^ (n k + 1) := by
  have h_roundStep : ‖paramSeq n a k - 1‖ ≤ (1 / 2) * (n k + 1) * ‖a k‖ ^ (n k + 1) := by
    rw [ paramSeq_leader _ _ _ hk ];
    unfold roundStep; split_ifs <;> norm_num;
    · gcongr;
      · convert abs_sub_round ( taylorCoeff ( PPfun n a k ) ( n k + 1 ) |> Complex.re ) |> le_trans <| ?_ using 1;
        · have := taylorCoeff_PPfun_real H hk ( n k + 1 ) ; simp_all +decide [ Complex.normSq, Complex.norm_def ] ;
          rw [ Real.sqrt_mul_self_eq_abs, abs_sub_comm ];
        · norm_num;
      · norm_cast;
    · have h_round : ‖(round (taylorCoeff (PPfun n a k) (n k + 1)).re : ℂ) - taylorCoeff (PPfun n a k) (n k + 1)‖ ≤ 1 / 2 := by
        have h_round : |(round (taylorCoeff (PPfun n a k) (n k + 1)).re : ℝ) - (taylorCoeff (PPfun n a k) (n k + 1)).re| ≤ 1 / 2 := by
          convert abs_sub_round ( ( taylorCoeff ( PPfun n a k ) ( n k + 1 ) |> Complex.re ) ) using 1;
          rw [ abs_sub_comm ];
        convert h_round using 1;
        convert Complex.norm_real _ using 2 ; norm_num [ Complex.ext_iff ];
        exact taylorCoeff_PPfun_real H hk _;
      norm_cast at *;
      exact le_trans ( div_le_self ( by positivity ) ( by norm_num ) ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right h_round ( by positivity ) ) ( by positivity ) );
  exact h_roundStep.trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) ( by positivity ) ) ( by positivity ) )

theorem paramSeq_bound (H : PairedEnum n a) (k : ℕ) :
    ‖paramSeq n a k - 1‖ ≤ Real.sqrt 2 / 2 * (n k + 1) * ‖a k‖ ^ (n k + 1) := by
  by_cases hk : 1 ≤ k ∧ n (k - 1) = n k;
  · by_cases hre : (a (k - 1)).im = 0 <;> simp_all +decide [ paramSeq_partner_pair, paramSeq_partner_real ];
    · positivity;
    · convert paramSeq_bound_leader H ( show IsLeader n ( k - 1 ) from ?_ ) using 1;
      · simp +decide [ Complex.norm_def, Complex.normSq ];
      · rcases k with ( _ | k ) <;> simp_all +decide;
        have := H.pair k; aesop;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ IsLeader ];
        exact fun h => H.le2 k <| by linarith;
  · exact paramSeq_bound_leader H hk

/-
One-step coefficient update at the affine-controlled degree.
-/
theorem taylorCoeff_PPfun_succ (H : PairedEnum n a) (k : ℕ) :
    taylorCoeff (PPfun n a (k + 1)) (n k + 1)
      = taylorCoeff (PPfun n a k) (n k + 1)
        + (paramSeq n a k - 1) / ((n k + 1) * (a k) ^ (n k + 1)) := by
  convert taylorCoeff_mul_E_succ ( PPfun_analyticAt n a k ) ( PPfun_zero_val n a k ) ( H.ha0 k ) ( n k ) using 1

theorem PairedEnum.n_lower (H : PairedEnum n a) (k : ℕ) : k ≤ 2 * n k + 1 := by
  induction' k using Nat.strong_induction_on with k ih;
  rcases k with ( _ | _ | k ) <;> simp +arith +decide [ * ];
  linarith [ ih k ( by linarith ), H.mono ( by linarith : k ≤ k + 2 ), H.le2 k, Nat.succ_le_of_lt ( show n ( k + 2 ) > n k from lt_of_le_of_ne ( H.mono ( by linarith ) ) ( Ne.symm ( H.le2 k ) ) ) ]

theorem PairedEnum.nfin (H : PairedEnum n a) (m : ℕ) : {k | n k ≤ m}.Finite := by
  exact Set.finite_iff_bddAbove.mpr ⟨ 2 * m + 1, fun k hk => by linarith [ H.n_lower k, hk.out ] ⟩

theorem PairedEnum.nsum (H : PairedEnum n a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun k => t ^ n k) := by
  -- Since $t < 1$, the series $\sum_{j=0}^{\infty} t^j$ converges.
  have h_series : Summable (fun j : ℕ => t ^ j) := by
    exact summable_geometric_of_lt_one ht0 ht1;
  have h_summable : Summable (fun k => t ^ (k / 2 : ℕ)) := by
    have h_summable : Summable (fun p : ℕ × Fin 2 => t ^ p.1) := by
      exact .of_norm <| by simpa using Summable.mul_norm ( h_series.norm ) ( show Summable fun p : Fin 2 => ‖(1 : ℝ)‖ from ⟨ _, hasSum_fintype _ ⟩ ) ;
    convert h_summable.comp_injective ( show Function.Injective ( fun k : ℕ => ( k / 2, ⟨ k % 2, Nat.mod_lt _ ( by decide ) ⟩ ) ) from fun a b h => by have := Nat.div_add_mod a 2; have := Nat.div_add_mod b 2; aesop ) using 1;
  refine' h_summable.of_nonneg_of_le ( fun k => pow_nonneg ht0 _ ) ( fun k => _ );
  exact pow_le_pow_of_le_one ht0 ht1.le ( by linarith [ Nat.div_mul_le_self k 2, H.n_lower k ] )

/-- **Freezing.** Multiplying by factors of order `≥ m` does not change the degree-`m`
coefficient. -/
theorem PPfun_freeze (_H : PairedEnum n a) (m K1 K2 : ℕ) (hle : K1 ≤ K2)
    (hfr : ∀ j, K1 ≤ j → j < K2 → m ≤ n j) :
    taylorCoeff (PPfun n a K2) m = taylorCoeff (PPfun n a K1) m := by
  revert K1 K2;
  intro K1 K2 hle hfr; induction' hle with K2 hle ih <;> simp_all +decide [ PPfun_succ ] ;
  rw [ ← ih fun j hj₁ hj₂ => hfr j hj₁ ( by linarith ), taylorCoeff_mul_E_eq_of_le ( PPfun_analyticAt n a K2 ) ( hfr K2 hle le_rfl ) ]

/-
Completion of a lone (arity-one, necessarily real) slot: after its single
factor, the affine-controlled coefficient is an integer.
-/
theorem coeff_leader_lone (H : PairedEnum n a) {L : ℕ} (hL : IsLeader n L)
    (hlone : n L < n (L + 1)) :
    ∃ z : ℤ, taylorCoeff (PPfun n a (L + 1)) (n L + 1) = z := by
  -- Since $a L$ is real, we have $(a L).im = 0$.
  have h_im_zero : (a L).im = 0 := by
    contrapose! hlone; have := H.nonreal L; simp_all +decide [ IsLeader ] ;
    grind;
  rw [ taylorCoeff_PPfun_succ ];
  · rw [ paramSeq_leader _ _ _ hL, roundStep ];
    by_cases h : a L = 0 <;> simp_all +decide [ mul_assoc, mul_div_assoc ];
    · exact absurd h ( H.ha0 L );
    · rw [ mul_div, mul_div_mul_left ] <;> norm_cast ; norm_num [ h ];
  · exact H

/-
Completion of a two-element slot (conjugate pair or pair of reals): after both
factors, the affine-controlled coefficient is an integer.
-/
theorem coeff_leader_pair (H : PairedEnum n a) {L : ℕ} (hL : IsLeader n L)
    (hpr : n (L + 1) = n L) :
    ∃ z : ℤ, taylorCoeff (PPfun n a (L + 2)) (n L + 1) = z := by
  -- By definition of $paramSeq$, we know that $paramSeq n a L = 1$ or $paramSeq n a L = T - v$.
  by_cases h_im : (a L).im = 0;
  · have := paramSeq_partner_real n a ( L + 1 ) ⟨ Nat.le_add_left 1 L, by aesop ⟩ ; simp_all +decide ;
    have := taylorCoeff_PPfun_succ H L; have := taylorCoeff_PPfun_succ H ( L + 1 ) ; simp_all +decide [ PPfun_succ ] ;
    rw [ paramSeq_leader n a L hL ];
    unfold roundStep; simp +decide [ h_im ] ;
    rw [ mul_assoc, mul_div_cancel_right₀ _ ( mul_ne_zero ( Nat.cast_add_one_ne_zero _ ) ( pow_ne_zero _ ( H.ha0 _ ) ) ) ] ; ring_nf ; norm_cast ; aesop;
  · have h_taylor : taylorCoeff (PPfun n a (L + 2)) (n L + 1) = taylorCoeff (PPfun n a L) (n L + 1) + (paramSeq n a L - 1) / ((n L + 1) * (a L) ^ (n L + 1)) + (starRingEnd ℂ (paramSeq n a L) - 1) / ((n L + 1) * (starRingEnd ℂ (a L)) ^ (n L + 1)) := by
      have h_taylor : taylorCoeff (PPfun n a (L + 2)) (n L + 1) = taylorCoeff (PPfun n a (L + 1)) (n L + 1) + (paramSeq n a (L + 1) - 1) / ((n L + 1) * (a (L + 1)) ^ (n L + 1)) := by
        convert taylorCoeff_PPfun_succ H ( L + 1 ) using 1; all_goals rw [ hpr ];
      rw [ h_taylor, taylorCoeff_PPfun_succ H L ];
      have := H.pair L; simp_all +decide [ IsLeader ] ;
      grind +locals;
    have h_taylor_real : (taylorCoeff (PPfun n a L) (n L + 1)).im = 0 := by
      apply taylorCoeff_PPfun_real H hL;
    have h_taylor_real : (paramSeq n a L - 1) / ((n L + 1) * (a L) ^ (n L + 1)) = (round (taylorCoeff (PPfun n a L) (n L + 1)).re - taylorCoeff (PPfun n a L) (n L + 1)) / 2 := by
      rw [ paramSeq_leader n a L hL ];
      unfold roundStep; simp +decide [ h_im ] ;
      rw [ div_eq_iff ( mul_ne_zero ( Nat.cast_add_one_ne_zero _ ) ( pow_ne_zero _ ( H.ha0 _ ) ) ) ] ; ring;
    have h_taylor_real : (starRingEnd ℂ (paramSeq n a L) - 1) / ((n L + 1) * (starRingEnd ℂ (a L)) ^ (n L + 1)) = (round (taylorCoeff (PPfun n a L) (n L + 1)).re - taylorCoeff (PPfun n a L) (n L + 1)) / 2 := by
      convert congr_arg Star.star h_taylor_real using 1 ; norm_num [ Complex.ext_iff, div_eq_mul_inv ];
      simp +decide [ Complex.ext_iff, ‹ ( taylorCoeff ( PPfun n a L ) ( n L + 1 ) |> Complex.im ) = 0 › ];
    simp_all +decide [ Complex.ext_iff ];
    exact ⟨ round ( taylorCoeff ( PPfun n a L ) ( n L + 1 ) |> Complex.re ), by ring ⟩

/-
**The integrality output.** Whenever `range K` includes every factor of order
`≤ m`, the degree-`m` coefficient of the partial product is an integer.
-/
theorem paramSeq_coeff_int (H : PairedEnum n a) (m K : ℕ)
    (hsub : {j | n j ≤ m} ⊆ ↑(Finset.range K)) :
    ∃ z : ℤ,
      taylorCoeff (fun w => ∏ j ∈ Finset.range K, E (n j) (paramSeq n a j) (w / a j)) m = z := by
  by_cases hm : m = 0;
  · use 1; simp [hm, taylorCoeff];
    unfold E; norm_num;
    exact Finset.prod_eq_one fun x hx => by rw [ Finset.sum_eq_zero fun y hy => by rw [ zero_pow ( by linarith [ Finset.mem_Icc.mp hy ] ) ] ; ring ] ; norm_num;
  · -- Let `B := Nat.find ‹∃ k, m ≤ n k›`.
    obtain ⟨B, hB⟩ : ∃ B, m ≤ n B ∧ ∀ j < B, n j < m := by
      have hB : ∃ B, m ≤ n B := by
        contrapose! hsub;
        exact Set.not_subset.mpr ⟨ K, by simp +decide [ le_of_lt ( hsub K ) ], by simp +decide ⟩;
      exact ⟨ Nat.find hB, Nat.find_spec hB, fun j hj => not_le.1 fun h => Nat.find_min hB hj h ⟩;
    have h_freeze : taylorCoeff (PPfun n a K) m = taylorCoeff (PPfun n a B) m := by
      apply PPfun_freeze H m B K (by
      have := @hsub ( B - 1 ) ; rcases B with ( _ | B ) <;> simp_all +decide ;
      exact this ( le_of_lt ( hB.2 B le_rfl ) )) (by
      exact fun j hj₁ hj₂ => hB.1.trans ( H.mono hj₁ ));
    -- It remains to show `∃ z, taylorCoeff (PPfun n a B) m = z`. Note `m = n (B-1) + 1` (since `n (B-1) = m-1`, `m ≥ 1`).
    have h_m_eq : m = n (B - 1) + 1 := by
      rcases B with ( _ | B ) <;> simp_all +decide;
      · linarith [ H.n0, Nat.pos_of_ne_zero hm ];
      · linarith [ hB.2 B le_rfl, H.contig B ];
    by_cases hB_ge_2 : B ≥ 2 ∧ n (B - 2) = m - 1;
    · have h_coeff_leader_pair : ∃ z : ℤ, taylorCoeff (PPfun n a (B - 2 + 2)) (n (B - 2) + 1) = z := by
        apply coeff_leader_pair H;
        · rcases B with ( _ | _ | B ) <;> simp_all +decide [ IsLeader ];
          exact fun _ => fun h => H.le2 ( B - 1 ) <| by cases B <;> aesop;
        · grind;
      rw [ ← PPfun_eq_prod ] ; aesop;
    · convert coeff_leader_lone H ( show IsLeader n ( B - 1 ) from ?_ ) ( show n ( B - 1 ) < n ( ( B - 1 ) + 1 ) from ?_ ) using 1;
      · rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ];
        rw [ ← h_m_eq, ← h_freeze, PPfun_eq_prod ];
      · rcases B with ( _ | _ | B ) <;> simp_all +decide [ IsLeader ];
      · rcases B with ( _ | _ | B ) <;> simp_all +decide

/-! ## The rounding output -/

/-- **Paired rounding.** From an enumeration `(n, a)` organized into conjugate/real
slots, the parameters `paramSeq n a` satisfy the rounding bound and make every
partial-product coefficient (once its slot is complete) an integer. -/
theorem exists_rounding (H : PairedEnum n a) :
    (∀ k, ‖paramSeq n a k - 1‖ ≤ Real.sqrt 2 / 2 * (n k + 1) * ‖a k‖ ^ (n k + 1)) ∧
    (∀ m K, {j | n j ≤ m} ⊆ ↑(Finset.range K) →
      ∃ z : ℤ,
        taylorCoeff (fun w => ∏ j ∈ Finset.range K, E (n j) (paramSeq n a j) (w / a j)) m
          = z) :=
  ⟨paramSeq_bound H, paramSeq_coeff_int H⟩

end Weierstrass