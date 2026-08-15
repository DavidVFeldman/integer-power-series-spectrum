import SpectrumFormalization.RealRing
import SpectrumFormalization.PowerSeriesFun

/-!
# Point-evaluation ideals (sequel, Section on point-evaluation ideals)

For `a ∈ 𝔻`, evaluation `ev_a : f ↦ f(a)` is a ring homomorphism on `𝒪(𝔻)`
(hence on the subrings `ℛ_ℝ` and `ℛ`). We formalize:

* `pointIdealRR_isPrime` / `pointIdealR_isPrime` — **Proposition (primeness)**:
  `P_a = ker(ev_a)` is prime for every `a ∈ 𝔻`.
* `pointIdealRR_isMaximal_real` — **Proposition (maximality for real points)**:
  `P_a` is maximal in `ℛ_ℝ` for real `a ∈ 𝔻`, with `ℛ_ℝ/P_a ≅ ℝ`.
* `pointIdealR_isMaximal` — **Proposition (maximality in `ℛ`)**: `P_a` is
  maximal in `ℛ` for every `a ∈ 𝔻`, with `ℛ/P_a ≅ ℂ`.

The maximality proofs go through the paper's bounded radix expansion, realized
via the `psFun` power-series building block.
-/

open Complex Weierstrass

namespace RequestProject

/-! ## Point evaluation as a ring homomorphism -/

/-- Evaluation at `a ∈ 𝔻` as a ring homomorphism on `OD = 𝒪(𝔻)`. -/
noncomputable def ODevalAt (a : ℂ) (ha : a ∈ 𝔻) : OD →+* ℂ :=
  Ideal.Quotient.lift vanishIdeal
    ((Pi.evalRingHom (fun _ : ℂ => ℂ) a).comp diskAnalytic.subtype)
    (fun _ hf => hf a ha)

@[simp] theorem ODevalAt_mk (a : ℂ) (ha : a ∈ 𝔻) (f : diskAnalytic) :
    ODevalAt a ha (ODmk f) = (f : ℂ → ℂ) a := rfl

/-- The point-evaluation ideal `P_a = ker(ev_a)` of `ℛ_ℝ`. -/
noncomputable def pointIdealRR (a : ℂ) (ha : a ∈ 𝔻) : Ideal RRsub :=
  RingHom.ker ((ODevalAt a ha).comp RRsub.subtype)

/-- The point-evaluation ideal `P_a = ker(ev_a)` of `ℛ`. -/
noncomputable def pointIdealR (a : ℂ) (ha : a ∈ 𝔻) : Ideal Rsub :=
  RingHom.ker ((ODevalAt a ha).comp Rsub.subtype)

/-! ## Primeness -/

/-- **Primeness of `P_a` in `ℛ_ℝ`.** -/
theorem pointIdealRR_isPrime (a : ℂ) (ha : a ∈ 𝔻) : (pointIdealRR a ha).IsPrime :=
  RingHom.ker_isPrime _

/-- **Primeness of `P_a` in `ℛ`.** -/
theorem pointIdealR_isPrime (a : ℂ) (ha : a ∈ 𝔻) : (pointIdealR a ha).IsPrime :=
  RingHom.ker_isPrime _

/-! ## Realness of values on `ℛ_ℝ` at real points -/

/-
At a real point `a ∈ 𝔻`, an integer-coefficient function takes a real value.
-/
theorem eval_real_of_isIntegerCoeffs {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g 𝔻)
    (hgi : IsIntegerCoeffs g) {a : ℝ} (ha : (a : ℂ) ∈ 𝔻) :
    ∃ r : ℝ, g (a : ℂ) = (r : ℂ) := by
  have := analyticOnNhd_𝔻_hasSum hg ha;
  -- Since $taylorCoeff g n$ is an integer for all $n$, each term in the series is real.
  have h_real : ∀ n, ∃ r : ℝ, taylorCoeff g n * a ^ n = r := by
    intro n
    obtain ⟨k, hk⟩ := hgi n
    use k * a ^ n
    simp [hk];
    exact Or.inl hk.symm
  generalize_proofs at *; (
  choose r hr using h_real; use ∑' n, r n; simp_all +decide [ Complex.ext_iff, tsum_mul_left ] ;
  have := this.tsum_eq; norm_cast at *; simp_all +decide [ Complex.ext_iff, tsum_mul_left ] ;)

/-! ## The bounded radix expansions (core analysis) -/

/-
**Real bounded radix expansion.** For `a ∈ (-1,1) \ {0}` and any real `w`,
there is a bounded integer sequence `c` with `∑' n, cₙ aⁿ = w`.
-/
theorem exists_radix_real {a : ℝ} (ha0 : a ≠ 0) (ha1 : |a| < 1) (w : ℝ) :
    ∃ c : ℕ → ℤ, (∃ C : ℝ, ∀ n, |(c n : ℝ)| ≤ C) ∧
      HasSum (fun n => (c n : ℝ) * a ^ n) w := by
  -- Define the sequence t recursively.
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t 0 = w ∧ ∀ n, t (n + 1) = t n - round (t n / a ^ n) * a ^ n := by
    exact ⟨ fun n => Nat.recOn n w fun n ih => ih - round ( ih / a ^ n ) * a ^ n, rfl, fun n => rfl ⟩;
  -- Define the sequence c recursively.
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℤ, ∀ n, c n = round (t n / a ^ n) := by
    exact ⟨ _, fun n => rfl ⟩;
  -- Show that the sequence c is bounded.
  have hc_bounded : ∃ C : ℝ, ∀ n, |(c n : ℝ)| ≤ C := by
    -- By induction, we can show that |t (n + 1)| ≤ (1/2) * |a| ^ n.
    have ht_bound : ∀ n, |t (n + 1)| ≤ (1 / 2) * |a| ^ n := by
      intro n
      rw [ht.right n]
      have h_round : |t n - round (t n / a ^ n) * a ^ n| ≤ (1 / 2) * |a| ^ n := by
        have h_round : |t n / a ^ n - round (t n / a ^ n)| ≤ 1 / 2 := by
          exact abs_sub_round _;
        rw [ show t n - ↑ ( round ( t n / a ^ n ) ) * a ^ n = ( t n / a ^ n - ↑ ( round ( t n / a ^ n ) ) ) * a ^ n by rw [ sub_mul, div_mul_cancel₀ _ ( pow_ne_zero _ ha0 ) ] ] ; rw [ abs_mul, abs_pow ] ; exact mul_le_mul_of_nonneg_right h_round ( by positivity ) ;
      exact h_round;
    -- For n ≥ 1, |c n| ≤ |t n / a^n| + 1/2 ≤ 1/(2|a|) + 1/2.
    have hc_bound_ge_one : ∀ n ≥ 1, |(c n : ℝ)| ≤ 1 / (2 * |a|) + 1 / 2 := by
      intros n hn
      have h_abs : |(c n : ℝ)| ≤ |t n / a ^ n| + 1 / 2 := by
        rw [ hc ];
        rw [ round_eq ];
        cases abs_cases ( t n / a ^ n ) <;> cases abs_cases ( ⌊t n / a ^ n + 1 / 2⌋ : ℝ ) <;> linarith [ Int.floor_le ( t n / a ^ n + 1 / 2 ), Int.lt_floor_add_one ( t n / a ^ n + 1 / 2 ) ];
      rcases n <;> simp_all +decide [ abs_div, pow_succ' ];
      refine le_trans h_abs ?_;
      exact add_le_add ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ ht_bound ‹_›, abs_pos.mpr ha0, pow_pos ( abs_pos.mpr ha0 ) ‹_›, mul_inv_cancel₀ ( ne_of_gt ( abs_pos.mpr ha0 ) ) ] ) le_rfl;
    use Max.max ( |(c 0 : ℝ)| ) ( 1 / ( 2 * |a| ) + 1 / 2 );
    exact fun n => if hn : n ≥ 1 then le_trans ( hc_bound_ge_one n hn ) ( le_max_right _ _ ) else by interval_cases n ; norm_num;
  -- Show that the series $\sum_{n=0}^{\infty} c_n a^n$ converges to $w$.
  have h_sum : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (c n : ℝ) * a ^ n) Filter.atTop (nhds w) := by
    have h_sum : ∀ N, ∑ n ∈ Finset.range N, (c n : ℝ) * a ^ n = w - t N := by
      intro N; induction N <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
    -- Show that the sequence t tends to 0.
    have ht_zero : Filter.Tendsto t Filter.atTop (nhds 0) := by
      have ht_zero : ∀ n, |t (n + 1)| ≤ (1 / 2) * |a| ^ n := by
        intro n
        have h_t_succ : |t (n + 1)| = |a|^n * |t n / a^n - round (t n / a^n)| := by
          rw [ ht.2, ← abs_pow, ← abs_mul ] ; ring_nf ; aesop;
        rw [ h_t_succ, mul_comm ];
        exact mul_le_mul_of_nonneg_right ( abs_sub_round _ ) ( by positivity );
      rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; exact squeeze_zero_norm ( fun n => ht_zero n ) ( by simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( abs_nonneg a ) ha1 ) ) ;
    simpa only [ h_sum, sub_zero ] using tendsto_const_nhds.sub ht_zero;
  refine' ⟨ c, hc_bounded, _ ⟩;
  rw [ hasSum_iff_tendsto_nat_of_summable_norm ];
  · convert h_sum using 1;
  · exact Summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) ( fun n => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( hc_bounded.choose_spec n ) ( pow_nonneg ( abs_nonneg a ) n ) ) ( Summable.mul_left _ <| summable_geometric_of_lt_one ( abs_nonneg a ) ha1 )

/-
**Gaussian bounded radix expansion.** For `a ∈ 𝔻 \ {0}` and any `w ∈ ℂ`,
there is a sequence of Gaussian integers `c` (bounded in norm) with
`∑' n, cₙ aⁿ = w`.
-/
theorem exists_radix_gaussian {a : ℂ} (ha0 : a ≠ 0) (ha1 : ‖a‖ < 1) (w : ℂ) :
    ∃ c : ℕ → GaussianInt, (∃ C : ℝ, ∀ n, ‖(c n : ℂ)‖ ≤ C) ∧
      HasSum (fun n => (c n : ℂ) * a ^ n) w := by
  -- Define the remainder t.
  set t : ℕ → ℂ := fun n => Nat.recOn n w (fun n tn => tn - (Weierstrass.nearestGaussianInt (tn / a ^ n) : ℂ) * a ^ n) with ht_def;
  -- Step 1 (remainder bound): For every n ≥ 1, ‖t_n‖ ≤ (√2/2) * ‖a‖^(n-1).
  have ht_bound : ∀ n ≥ 1, ‖t n‖ ≤ (Real.sqrt 2 / 2) * ‖a‖ ^ (n - 1) := by
    intro n hn
    induction' n, hn using Nat.le_induction with n hn ih;
    · have := Weierstrass.norm_sub_nearestGaussianInt_le ( w / a ^ 0 ) ; aesop;
    · have := Weierstrass.norm_sub_nearestGaussianInt_le ( t n / a ^ n ) ; simp_all +decide [ pow_succ, mul_assoc, mul_div_cancel₀ ] ;
      convert mul_le_mul_of_nonneg_right this ( pow_nonneg ( norm_nonneg a ) n ) using 1 ; rw [ div_sub', norm_div ] <;> norm_num [ ha0 ] ; ring;
      grind;
  -- Step 3 (coefficient bound): There is `C` with `∀ n, ‖(c n:ℂ)‖ ≤ C`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, ‖(Weierstrass.nearestGaussianInt (t n / a ^ n) : ℂ)‖ ≤ C := by
    -- For n ≥ 1, we have ‖t n / a^n‖ ≤ (√2/2) / ‖a‖.
    have ht_div_bound : ∀ n ≥ 1, ‖t n / a ^ n‖ ≤ (Real.sqrt 2 / 2) / ‖a‖ := by
      intro n hn; specialize ht_bound n hn; rcases n <;> simp_all +decide [ pow_succ, div_mul_eq_div_div ] ;
      rw [ div_div, div_le_div_iff₀ ] <;> first | positivity | nlinarith [ norm_pos_iff.mpr ha0, pow_pos ( norm_pos_iff.mpr ha0 ) ‹_› ] ;
    -- For n ≥ 1, we have ‖nearestGaussianInt (t n / a^n)‖ ≤ ‖t n / a^n‖ + √2/2.
    have ht_nearest_bound : ∀ n ≥ 1, ‖(Weierstrass.nearestGaussianInt (t n / a ^ n) : ℂ)‖ ≤ ‖t n / a ^ n‖ + Real.sqrt 2 / 2 := by
      intro n hn; have := Weierstrass.norm_sub_nearestGaussianInt_le ( t n / a ^ n ) ; simp_all +decide [ dist_eq_norm ] ;
      have := norm_sub_le ( ( t n : ℂ ) / a ^ n - GaussianInt.toComplex ( nearestGaussianInt ( t n / a ^ n ) ) ) ( ( t n : ℂ ) / a ^ n ) ; simp_all +decide [ norm_div ] ; linarith;
    use Max.max ( ‖GaussianInt.toComplex ( nearestGaussianInt w )‖ ) ( Real.sqrt 2 / 2 / ‖a‖ + Real.sqrt 2 / 2 );
    intro n; by_cases hn : 1 ≤ n <;> simp_all +decide ;
    exact Or.inr ( le_trans ( ht_nearest_bound n hn ) ( add_le_add ( ht_div_bound n hn ) le_rfl ) );
  refine' ⟨ fun n => Weierstrass.nearestGaussianInt ( t n / a ^ n ), ⟨ C, hC ⟩, _ ⟩;
  -- Step 4 (summability and sum): `‖(c n:ℂ) * a^n‖ ≤ C * ‖a‖^n`, and `∑ C ‖a‖^n` converges (`‖a‖ < 1`), so the series is (absolutely) summable with some sum `S`.
  have h_summable : Summable (fun n => (Weierstrass.nearestGaussianInt (t n / a ^ n) : ℂ) * a ^ n) := by
    -- By comparison, it suffices to show that the series $\sum_{n=0}^{\infty} C |a|^n$ converges.
    have h_comparison : Summable (fun n => C * ‖a‖ ^ n) := by
      exact Summable.mul_left _ <| summable_geometric_of_lt_one ( norm_nonneg a ) ha1;
    exact Summable.of_norm <| by simpa using h_comparison.of_nonneg_of_le ( fun n => by positivity ) fun n => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_right ( hC n ) ( by positivity ) ;
  -- By definition of $t$, we know that $\sum_{k=0}^{N-1} c_k a^k = w - t_N$.
  have h_partial_sum : ∀ N, ∑ k ∈ Finset.range N, (Weierstrass.nearestGaussianInt (t k / a ^ k) : ℂ) * a ^ k = w - t N := by
    intro N; induction N <;> simp_all +decide [ Finset.sum_range_succ ] ; ring;
  -- Since $t_N \to 0$ as $N \to \infty$, we have $w - t_N \to w$.
  have h_tendsto_zero : Filter.Tendsto t Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => ht_bound n hn ⟩ ) ( by simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( norm_nonneg a ) ha1 |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat 1 ) );
  convert h_summable.hasSum using 1;
  exact tendsto_nhds_unique ( by simpa using h_tendsto_zero.const_sub w ) ( h_summable.hasSum.tendsto_sum_nat.congr ( by aesop ) )

/-! ## Surjectivity of evaluation -/

/-- **Surjectivity onto `ℝ`.** For real `a ∈ 𝔻 \ {0}` and any real `w`, some
element of `ℛ_ℝ` evaluates to `w` at `a`. -/
theorem exists_RR_eval_eq {a : ℝ} (ha : (a : ℂ) ∈ 𝔻) (ha0 : a ≠ 0) (w : ℝ) :
    ∃ x : RRsub, (ODevalAt (a : ℂ) ha) (RRsub.subtype x) = (w : ℂ) := by
  have ha1 : |a| < 1 := by
    rw [mem_𝔻_iff] at ha; simpa using ha
  obtain ⟨c, ⟨C, hC⟩, hsum⟩ := exists_radix_real ha0 ha1 w
  -- The realizing function.
  set cc : ℕ → ℂ := fun n => (c n : ℂ) with hcc
  have hbound : ∀ n, ‖cc n‖ ≤ C := by
    intro n; simp only [hcc, Complex.norm_intCast]; exact hC n
  have hanalytic : AnalyticOnNhd ℂ (psFun cc) 𝔻 := psFun_analyticOnNhd hbound
  have hint : IsIntegerCoeffs (psFun cc) := by
    intro m
    rw [psFun_taylorCoeff hbound m]
    exact ⟨c m, rfl⟩
  refine ⟨⟨ODmk ⟨psFun cc, hanalytic⟩, ?_⟩, ?_⟩
  · exact ⟨⟨psFun cc, hanalytic⟩, hint, rfl⟩
  · show ODevalAt (a : ℂ) ha (ODmk ⟨psFun cc, hanalytic⟩) = (w : ℂ)
    rw [ODevalAt_mk]
    show psFun cc (a : ℂ) = (w : ℂ)
    have h1 : HasSum (fun n => cc n * (a : ℂ) ^ n) (psFun cc (a : ℂ)) :=
      psFun_hasSum hbound ha
    have h2 : HasSum (fun n => cc n * (a : ℂ) ^ n) (w : ℂ) := by
      have h := Complex.ofRealCLM.hasSum hsum
      simpa [hcc, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_intCast] using h
    exact h1.unique h2

/-- **Surjectivity onto `ℂ`.** For `a ∈ 𝔻 \ {0}` and any `w ∈ ℂ`, some element of
`ℛ` evaluates to `w` at `a`. -/
theorem exists_R_eval_eq {a : ℂ} (ha : a ∈ 𝔻) (ha0 : a ≠ 0) (w : ℂ) :
    ∃ x : Rsub, (ODevalAt a ha) (Rsub.subtype x) = w := by
  have ha1 : ‖a‖ < 1 := by rw [mem_𝔻_iff] at ha; exact ha
  obtain ⟨c, ⟨C, hC⟩, hsum⟩ := exists_radix_gaussian ha0 ha1 w
  set cc : ℕ → ℂ := fun n => (c n : ℂ) with hcc
  have hbound : ∀ n, ‖cc n‖ ≤ C := hC
  have hanalytic : AnalyticOnNhd ℂ (psFun cc) 𝔻 := psFun_analyticOnNhd hbound
  have hgauss : IsGaussianCoeffs (psFun cc) := by
    intro m
    rw [psFun_taylorCoeff hbound m]
    exact ⟨c m, rfl⟩
  refine ⟨⟨ODmk ⟨psFun cc, hanalytic⟩, ?_⟩, ?_⟩
  · exact ⟨⟨psFun cc, hanalytic⟩, hgauss, rfl⟩
  · show ODevalAt a ha (ODmk ⟨psFun cc, hanalytic⟩) = w
    rw [ODevalAt_mk]
    show psFun cc a = w
    exact (psFun_hasSum hbound ha).unique hsum

/-! ## Maximality in `ℛ` (Gaussian ring) -/

/-- **Maximality in `ℛ`.** For every `a ∈ 𝔻` with `a ≠ 0`, `P_a` is maximal in
`ℛ`, since `ev_a : ℛ → ℂ` is then surjective onto the field `ℂ`. (The point
`a = 0` is excluded: there `ev_0` has image `ℤ[i]`, so `P_0 = 𝔫₀` is not maximal,
cf. `fiberEquiv`. The paper's Proposition states "for each `a ∈ 𝔻`" but its
radix-expansion proof requires `a ≠ 0`.) -/
theorem pointIdealR_isMaximal {a : ℂ} (ha : a ∈ 𝔻) (ha0 : a ≠ 0) :
    (pointIdealR a ha).IsMaximal := by
  have hsurj : Function.Surjective ((ODevalAt a ha).comp Rsub.subtype) := by
    intro w
    obtain ⟨x, hx⟩ := exists_R_eval_eq ha ha0 w
    exact ⟨x, hx⟩
  exact RingHom.ker_isMaximal_of_surjective _ hsurj

/-! ## Maximality in `ℛ_ℝ` (real ring, real points) -/

/-- The subring `ℝ ⊆ ℂ` (image of `algebraMap ℝ ℂ`). -/
noncomputable def realSubring : Subring ℂ := (algebraMap ℝ ℂ).range

/-- `ℝ` is ring-isomorphic to the subring `ℝ ⊆ ℂ`. -/
noncomputable def realEquiv : ℝ ≃+* realSubring :=
  RingEquiv.ofBijective (algebraMap ℝ ℂ).rangeRestrict
    ⟨fun _ _ h => FaithfulSMul.algebraMap_injective ℝ ℂ (Subtype.ext_iff.mp h),
     (algebraMap ℝ ℂ).rangeRestrict_surjective⟩

theorem realEquiv_apply (r : ℝ) : (realEquiv r : ℂ) = (r : ℂ) := rfl

/-- Values on `ℛ_ℝ` at real points are real. -/
theorem ODevalAt_RR_mem_realSubring (a : ℝ) (ha : (a : ℂ) ∈ 𝔻) (x : RRsub) :
    (ODevalAt (a : ℂ) ha) (RRsub.subtype x) ∈ realSubring := by
  obtain ⟨f, hfi, hfx⟩ := mem_RRsub.mp x.2
  have hfa : (ODevalAt (a : ℂ) ha) (RRsub.subtype x) = (f : ℂ → ℂ) (a : ℂ) := by
    have : RRsub.subtype x = ODmk f := hfx.symm
    rw [this, ODevalAt_mk]
  rw [hfa]
  obtain ⟨r, hr⟩ := eval_real_of_isIntegerCoeffs f.2 hfi ha
  exact ⟨r, by simpa using hr.symm⟩

/-- **Evaluation at a real point, valued in `ℝ`.** -/
noncomputable def evRealAt (a : ℝ) (ha : (a : ℂ) ∈ 𝔻) : RRsub →+* ℝ :=
  realEquiv.symm.toRingHom.comp
    (((ODevalAt (a : ℂ) ha).comp RRsub.subtype).codRestrict realSubring
      (ODevalAt_RR_mem_realSubring a ha))

theorem ofReal_evRealAt (a : ℝ) (ha : (a : ℂ) ∈ 𝔻) (x : RRsub) :
    ((evRealAt a ha x : ℝ) : ℂ) = (ODevalAt (a : ℂ) ha) (RRsub.subtype x) := by
  have h := RingEquiv.apply_symm_apply realEquiv
    ⟨(ODevalAt (a : ℂ) ha) (RRsub.subtype x), ODevalAt_RR_mem_realSubring a ha x⟩
  have h2 : (realEquiv (evRealAt a ha x) : ℂ)
      = (ODevalAt (a : ℂ) ha) (RRsub.subtype x) := by
    rw [show evRealAt a ha x
        = realEquiv.symm ⟨(ODevalAt (a : ℂ) ha) (RRsub.subtype x),
          ODevalAt_RR_mem_realSubring a ha x⟩ from rfl, h]
  rw [realEquiv_apply] at h2
  exact h2

theorem pointIdealRR_eq_ker_evRealAt (a : ℝ) (ha : (a : ℂ) ∈ 𝔻) :
    pointIdealRR (a : ℂ) ha = RingHom.ker (evRealAt a ha) := by
  ext x
  simp only [pointIdealRR, RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro h
    have : ((evRealAt a ha x : ℝ) : ℂ) = 0 := by rw [ofReal_evRealAt]; exact h
    exact_mod_cast this
  · intro h
    have : ((evRealAt a ha x : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by rw [h]
    rw [ofReal_evRealAt] at this
    simpa using this

theorem evRealAt_surjective {a : ℝ} (ha : (a : ℂ) ∈ 𝔻) (ha0 : a ≠ 0) :
    Function.Surjective (evRealAt a ha) := by
  intro w
  obtain ⟨x, hx⟩ := exists_RR_eval_eq ha ha0 w
  refine ⟨x, ?_⟩
  have : ((evRealAt a ha x : ℝ) : ℂ) = ((w : ℝ) : ℂ) := by rw [ofReal_evRealAt, hx]
  exact_mod_cast this

/-- **Maximality for real points.** For real `a ∈ 𝔻` with `a ≠ 0`, `P_a` is
maximal in `ℛ_ℝ`, with `ℛ_ℝ/P_a ≅ ℝ`. -/
theorem pointIdealRR_isMaximal_real {a : ℝ} (ha : (a : ℂ) ∈ 𝔻) (ha0 : a ≠ 0) :
    (pointIdealRR (a : ℂ) ha).IsMaximal := by
  rw [pointIdealRR_eq_ker_evRealAt]
  exact RingHom.ker_isMaximal_of_surjective _ (evRealAt_surjective ha ha0)

end RequestProject