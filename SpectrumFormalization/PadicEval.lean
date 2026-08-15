import SpectrumFormalization.PrimesOutside

/-!
# `p`-adic evaluation primes (Tier D, `prop:padic`)

Fix a rational prime `p`. Every element of `ℛ_ℝ` has integer Taylor
coefficients `aₙ`, and the series `∑ₙ aₙ (-p)ⁿ` converges in `ℤ_[p]` because
`‖aₙ(-p)ⁿ‖ ≤ p⁻ⁿ`. The resulting map

`ψ_p : ℛ_ℝ → ℤ_[p]`, `ψ_p f = ∑ₙ aₙ (-p)ⁿ`

is a ring homomorphism, and we study its kernel `Q_p`.

The main outcome (`primes_outside_classification_false`) is that `Q_p` is a
nonzero prime that contains neither `z` nor any nonzero integer, and does **not**
lie in `𝔓₁`; in particular it is none of `(0)`, `(z)`, `(q)`, `(z,q)`. This
refutes the earlier classification of primes outside `𝔓₁` and shows that class
(c) of the spectrum trichotomy strictly contains `{⊥} ∪ 𝔓₁`.

We build the evaluation homomorphism at a general `α ∈ ℤ_[p]` with `‖α‖ < 1`
(the manuscript's `rem:padic` observes that any `α ∈ pℤ_p` works); the case
`α = -p` is singled out because of the base-`(-p)` digit expansion, which gives
surjectivity of `ψ_p` and hence non-maximality of `Q_p`.
-/

open Complex Weierstrass PowerSeries

namespace RequestProject

section PadicEval

variable (p : ℕ) [Fact p.Prime]

/-! ## D.1 — the evaluation homomorphism -/

/-- The formal `p`-adic evaluation of an integer power series at `α`. -/
noncomputable def psEvalFun (α : ℤ_[p]) (f : PowerSeries ℤ) : ℤ_[p] :=
  ∑' n : ℕ, ((PowerSeries.coeff (R := ℤ) n f : ℤ) : ℤ_[p]) * α ^ n

/-- Absolute (nonarchimedean) convergence of the evaluation series. -/
theorem summable_norm_psEval {α : ℤ_[p]} (hα : ‖α‖ < 1) (a : ℕ → ℤ) :
    Summable (fun n : ℕ => ‖((a n : ℤ) : ℤ_[p]) * α ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (norm_nonneg α) hα)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one _)

theorem summable_psEval {α : ℤ_[p]} (hα : ‖α‖ < 1) (a : ℕ → ℤ) :
    Summable (fun n : ℕ => ((a n : ℤ) : ℤ_[p]) * α ^ n) :=
  (summable_norm_psEval p hα a).of_norm

/-- **D.1.** `p`-adic evaluation at `α` with `‖α‖ < 1`, as a ring homomorphism
`ℤ⟦z⟧ → ℤ_[p]`. -/
noncomputable def psEval (α : ℤ_[p]) (hα : ‖α‖ < 1) : PowerSeries ℤ →+* ℤ_[p] where
  toFun f := psEvalFun p α f
  map_one' := by
    refine (tsum_eq_single 0 ?_).trans ?_
    · intro n hn
      simp [PowerSeries.coeff_one, hn]
    · simp
  map_zero' := by simp [psEvalFun]
  map_add' f g := by
    simp only [psEvalFun]
    rw [← Summable.tsum_add (summable_psEval p hα (fun n => PowerSeries.coeff (R := ℤ) n f))
      (summable_psEval p hα (fun n => PowerSeries.coeff (R := ℤ) n g))]
    refine tsum_congr fun n => ?_
    rw [map_add]
    push_cast
    ring
  map_mul' f g := by
    simp only [psEvalFun]
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (summable_norm_psEval p hα (fun n => PowerSeries.coeff (R := ℤ) n f))
      (summable_norm_psEval p hα (fun n => PowerSeries.coeff (R := ℤ) n g))]
    refine tsum_congr fun n => ?_
    rw [PowerSeries.coeff_mul]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have hkl' : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    subst hkl'
    ring

theorem psEval_apply (α : ℤ_[p]) (hα : ‖α‖ < 1) (f : PowerSeries ℤ) :
    psEval p α hα f = ∑' n : ℕ, ((PowerSeries.coeff (R := ℤ) n f : ℤ) : ℤ_[p]) * α ^ n := rfl

/-! ## The homomorphism `ψ_p` on `ℛ_ℝ` -/

theorem norm_neg_p_lt_one : ‖(-(p : ℤ_[p]))‖ < 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  rw [norm_neg, PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ hp

/-- **`ψ_p`**: the `p`-adic evaluation homomorphism `ℛ_ℝ → ℤ_[p]`,
`f = ∑ aₙ zⁿ ↦ ∑ aₙ (-p)ⁿ`. -/
noncomputable def psiP : RRsub →+* ℤ_[p] :=
  (psEval p (-(p : ℤ_[p])) (norm_neg_p_lt_one p)).comp coeffHom

theorem psiP_apply (f : RRsub) :
    psiP p f = ∑' n : ℕ, ((intCoeff f n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n := by
  simp only [psiP, RingHom.comp_apply, psEval_apply, coeff_coeffHom]

theorem summable_psiP (f : RRsub) :
    Summable (fun n : ℕ => ((intCoeff f n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n) :=
  summable_psEval p (norm_neg_p_lt_one p) (intCoeff f)

/-! ## D.2 — the kernel `Q_p` and its basic properties -/

/-- **`Q_p`**: the kernel of the `p`-adic evaluation homomorphism. -/
noncomputable def Qp : Ideal RRsub := RingHom.ker (psiP p)

theorem mem_Qp {f : RRsub} : f ∈ Qp p ↔ psiP p f = 0 := RingHom.mem_ker

/-- `ψ_p z = -p`. -/
theorem psiP_zElt : psiP p zElt = -(p : ℤ_[p]) := by
  rw [psiP_apply]
  refine (tsum_eq_single 1 ?_).trans ?_
  · intro n hn
    simp [intCoeff_zElt, hn]
  · simp

/-- `ψ_p` fixes integer constants. -/
theorem psiP_intCast (n : ℤ) : psiP p (n : RRsub) = (n : ℤ_[p]) := map_intCast _ n

/-- **`Q_p` is prime**, being the kernel of a homomorphism into the domain
`ℤ_[p]`. -/
theorem Qp_isPrime : (Qp p).IsPrime := RingHom.ker_isPrime _

/-- `z + p ∈ Q_p`. -/
theorem zElt_add_p_mem : zElt + (p : RRsub) ∈ Qp p := by
  rw [mem_Qp, map_add, psiP_zElt, map_natCast]
  ring

/-- `z + p ≠ 0` in `ℛ_ℝ` (its constant term is `p`). -/
theorem zElt_add_p_ne_zero : zElt + (p : RRsub) ≠ 0 := by
  intro h
  have hev : ev0RR (zElt + (p : RRsub)) = 0 := by rw [h, map_zero]
  rw [map_add, ev0RR_zElt, ev0RR_natCast, zero_add] at hev
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hev)

/-- `Q_p ≠ (0)`. -/
theorem Qp_ne_bot : Qp p ≠ ⊥ := by
  intro h
  have := zElt_add_p_mem p
  rw [h, Ideal.mem_bot] at this
  exact zElt_add_p_ne_zero p this

/-- `z ∉ Q_p`. -/
theorem zElt_not_mem_Qp : zElt ∉ Qp p := by
  rw [mem_Qp, psiP_zElt]
  intro h
  have hp : ((p : ℕ) : ℤ_[p]) = 0 := by
    have := neg_eq_zero.mp h
    exact_mod_cast this
  have : (p : ℕ) = 0 := by exact_mod_cast hp
  exact (Fact.out : p.Prime).ne_zero this

/-- `Q_p ∩ ℤ = 0`. -/
theorem intCast_mem_Qp_iff (n : ℤ) : (n : RRsub) ∈ Qp p ↔ n = 0 := by
  rw [mem_Qp, psiP_intCast]
  exact_mod_cast Iff.rfl

/-- **Reduction mod `p` of the evaluation.** `ψ_p f ≡ a₀ (mod p)`. -/
theorem psiP_mod_p (f : RRsub) :
    psiP p f - ((intCoeff f 0 : ℤ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
  set α : ℤ_[p] := -(p : ℤ_[p]) with hα
  have hsum := summable_psiP p f
  have hsplit : psiP p f
      = ((intCoeff f 0 : ℤ) : ℤ_[p]) * α ^ 0
        + ∑' n : ℕ, ((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ (n + 1) := by
    rw [psiP_apply]
    exact hsum.tsum_eq_zero_add
  have hshift : ∀ n : ℕ, ((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ (n + 1)
      = α * (((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ n) := by
    intro n; ring
  have hshiftsum : Summable (fun n : ℕ => ((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ n) :=
    summable_psEval p (norm_neg_p_lt_one p) (fun n => intCoeff f (n + 1))
  have htail : ∑' n : ℕ, ((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ (n + 1)
      = α * ∑' n : ℕ, ((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ n := by
    rw [tsum_congr hshift]
    exact (hshiftsum.hasSum.mul_left α).tsum_eq
  refine Ideal.mem_span_singleton.mpr ⟨-(∑' n : ℕ,
    ((intCoeff f (n + 1) : ℤ) : ℤ_[p]) * α ^ n), ?_⟩
  rw [hsplit, htail, hα]
  ring

/-- **`Q_p ∉ 𝔓₁`.** No element of `Q_p` has a unit constant term: the value of
`ψ_p` is congruent to the constant term mod `p`. -/
theorem Qp_not_isInP1 : ¬ IsInP1 (Qp p) := by
  rintro ⟨f, hf, hunit⟩
  have hzero : psiP p f = 0 := (mem_Qp p).mp hf
  have hmod := psiP_mod_p p f
  rw [hzero, zero_sub, Ideal.mem_span_singleton] at hmod
  have hdvd : (p : ℤ_[p]) ∣ ((intCoeff f 0 : ℤ) : ℤ_[p]) := (dvd_neg).mp hmod
  -- the constant term is `±1`, so `p` would divide a unit
  have hev : ev0RR f = intCoeff f 0 := ev0RR_eq f
  have hunit' : IsUnit (intCoeff f 0) := hev ▸ hunit
  have hone : IsUnit (((intCoeff f 0 : ℤ) : ℤ_[p])) := by
    rcases Int.isUnit_iff.mp hunit' with h | h <;> rw [h] <;> simp
  have hpunit : IsUnit ((p : ℕ) : ℤ_[p]) := isUnit_of_dvd_unit hdvd hone
  rw [PadicInt.isUnit_iff, PadicInt.norm_p] at hpunit
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  have : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  rw [hpunit] at this
  exact lt_irrefl 1 this

/-! ## D.3 — the counterexample package -/

/-- **D.3 (`prop:padic`).** The `p`-adic evaluation ideal `Q_p` is a nonzero
prime, containing neither `z` nor any nonzero integer, lying outside `𝔓₁`, and
different from every ideal in the earlier (erroneous) classification of primes
outside `𝔓₁`. -/
theorem primes_outside_classification_false :
    (Qp p).IsPrime ∧ Qp p ≠ ⊥ ∧ zElt ∉ Qp p ∧ (∀ n : ℤ, (n : RRsub) ∈ Qp p → n = 0) ∧
    ¬ IsInP1 (Qp p) ∧
    (∀ q : ℕ, q.Prime → Qp p ≠ Ideal.span {(q : RRsub)}) ∧
    (∀ q : ℕ, q.Prime → Qp p ≠ Ideal.span {zElt, (q : RRsub)}) ∧
    Qp p ≠ Ideal.span {zElt} := by
  refine ⟨Qp_isPrime p, Qp_ne_bot p, zElt_not_mem_Qp p,
    fun n hn => (intCast_mem_Qp_iff p n).mp hn, Qp_not_isInP1 p, ?_, ?_, ?_⟩
  · intro q hq hEq
    have hmem : ((q : ℕ) : RRsub) ∈ Qp p := by
      rw [hEq]; exact Ideal.subset_span rfl
    have hz : ((q : ℤ) : RRsub) ∈ Qp p := by exact_mod_cast hmem
    have := (intCast_mem_Qp_iff p (q : ℤ)).mp hz
    exact hq.ne_zero (by exact_mod_cast this)
  · intro q _ hEq
    exact zElt_not_mem_Qp p (by rw [hEq]; exact Ideal.subset_span (Set.mem_insert _ _))
  · intro hEq
    exact zElt_not_mem_Qp p (by rw [hEq]; exact Ideal.subset_span rfl)

/-! ## D.4 — surjectivity and non-maximality -/

theorem neg_p_dvd_sub_zmodRepr (x : ℤ_[p]) :
    (-(p : ℤ_[p])) ∣ (x - (PadicInt.zmodRepr x : ℤ_[p])) := by
  have hmem := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  exact neg_dvd.mpr hmem

/-- The remainder in the base-`(-p)` digit recursion. -/
noncomputable def padicRem (x : ℤ_[p]) : ℤ_[p] := (neg_p_dvd_sub_zmodRepr p x).choose

theorem padicRem_spec (x : ℤ_[p]) :
    x - (PadicInt.zmodRepr x : ℤ_[p]) = (-(p : ℤ_[p])) * padicRem p x :=
  (neg_p_dvd_sub_zmodRepr p x).choose_spec

/-- The `n`-th base-`(-p)` digit of `w ∈ ℤ_[p]`. -/
noncomputable def padicDigit (w : ℤ_[p]) (n : ℕ) : ℕ :=
  PadicInt.zmodRepr ((padicRem p)^[n] w)

theorem padicDigit_lt (w : ℤ_[p]) (n : ℕ) : padicDigit p w n < p :=
  PadicInt.zmodRepr_lt_p _

/-- **Base-`(-p)` expansion with remainder.** -/
theorem padic_expansion (w : ℤ_[p]) (N : ℕ) :
    w = (∑ n ∈ Finset.range N, ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n)
        + (-(p : ℤ_[p])) ^ N * ((padicRem p)^[N] w) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep : ((padicRem p)^[N] w) - ((padicDigit p w N : ℤ) : ℤ_[p])
          = (-(p : ℤ_[p])) * ((padicRem p)^[N + 1] w) := by
        have h := padicRem_spec p ((padicRem p)^[N] w)
        rw [Function.iterate_succ_apply']
        simpa [padicDigit] using h
      have hkey : ((padicDigit p w N : ℤ) : ℤ_[p])
          + (-(p : ℤ_[p])) * ((padicRem p)^[N + 1] w) = (padicRem p)^[N] w := by
        rw [← hstep]; ring
      rw [Finset.sum_range_succ]
      calc w = (∑ n ∈ Finset.range N, ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n)
              + (-(p : ℤ_[p])) ^ N * ((padicRem p)^[N] w) := ih
        _ = (∑ n ∈ Finset.range N, ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n)
              + (-(p : ℤ_[p])) ^ N *
                (((padicDigit p w N : ℤ) : ℤ_[p])
                  + (-(p : ℤ_[p])) * ((padicRem p)^[N + 1] w)) := by rw [hkey]
        _ = _ := by ring

/-- The remainder term tends to `0`. -/
theorem padic_tail_tendsto_zero (w : ℤ_[p]) :
    Filter.Tendsto (fun N : ℕ => (-(p : ℤ_[p])) ^ N * ((padicRem p)^[N] w))
      Filter.atTop (nhds 0) := by
  have hbound : ∀ N : ℕ, ‖(-(p : ℤ_[p])) ^ N * ((padicRem p)^[N] w)‖
      ≤ ‖(-(p : ℤ_[p]))‖ ^ N := by
    intro N
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)
  refine squeeze_zero_norm hbound ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_neg_p_lt_one p)

/-- **The digit series converges to `w`.** -/
theorem hasSum_padicDigits (w : ℤ_[p]) :
    HasSum (fun n : ℕ => ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n) w := by
  have hsummable : Summable
      (fun n : ℕ => ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n) :=
    summable_psEval p (norm_neg_p_lt_one p) (fun n => (padicDigit p w n : ℤ))
  obtain ⟨S, hS⟩ := hsummable
  have hpartial : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n) Filter.atTop (nhds S) :=
    hS.tendsto_sum_nat
  have hpartial' : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n) Filter.atTop (nhds w) := by
    have hrewrite : ∀ N : ℕ,
        (∑ n ∈ Finset.range N, ((padicDigit p w n : ℤ) : ℤ_[p]) * (-(p : ℤ_[p])) ^ n)
          = w - (-(p : ℤ_[p])) ^ N * ((padicRem p)^[N] w) := by
      intro N
      have := padic_expansion p w N
      linear_combination -this
    simp only [hrewrite]
    have := (padic_tail_tendsto_zero p w).const_sub w
    simpa using this
  have : S = w := tendsto_nhds_unique hpartial hpartial'
  exact this ▸ hS

/-- **D.4 (surjectivity).** `ψ_p` is surjective onto `ℤ_[p]`, by the base-`(-p)`
digit expansion. -/
theorem psiP_surjective : Function.Surjective (psiP p) := by
  intro w
  have hbound : ∀ n : ℕ, ‖((padicDigit p w n : ℤ) : ℂ)‖ ≤ (p : ℝ) := by
    intro n
    rw [Complex.norm_intCast]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((padicDigit p w n : ℤ) : ℝ))]
    exact_mod_cast (padicDigit_lt p w n).le
  refine ⟨mkIntSeq (fun n => (padicDigit p w n : ℤ)) (p : ℝ) hbound, ?_⟩
  rw [psiP_apply]
  have hcoeff : ∀ n : ℕ,
      intCoeff (mkIntSeq (fun n => (padicDigit p w n : ℤ)) (p : ℝ) hbound) n
        = (padicDigit p w n : ℤ) := intCoeff_mkIntSeq _ _ _
  simp only [hcoeff]
  exact (hasSum_padicDigits p w).tsum_eq

/-- `ℤ_[p]` is not a field: `p` is a nonzero nonunit. -/
theorem padicInt_not_isField : ¬ IsField ℤ_[p] := by
  intro hfield
  have hp0 : ((p : ℕ) : ℤ_[p]) ≠ 0 := by
    intro h
    have : (p : ℕ) = 0 := by exact_mod_cast h
    exact (Fact.out : p.Prime).ne_zero this
  obtain ⟨v, hv⟩ := hfield.mul_inv_cancel hp0
  have hunit : IsUnit ((p : ℕ) : ℤ_[p]) := IsUnit.of_mul_eq_one _ hv
  rw [PadicInt.isUnit_iff, PadicInt.norm_p] at hunit
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  have hlt : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  rw [hunit] at hlt
  exact lt_irrefl 1 hlt

/-- **D.4 (the quotient).** `ℛ_ℝ/Q_p ≅ ℤ_[p]`. -/
noncomputable def quotQpEquiv : (RRsub ⧸ Qp p) ≃+* ℤ_[p] :=
  RingHom.quotientKerEquivOfSurjective (psiP_surjective p)

/-- **D.4 (non-maximality).** `Q_p` is not maximal: the quotient `ℛ_ℝ/Q_p` is
isomorphic to `ℤ_[p]`, which is not a field. -/
theorem Qp_not_isMaximal : ¬ (Qp p).IsMaximal := by
  intro hmax
  have hfieldQ : IsField (RRsub ⧸ Qp p) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax
  exact padicInt_not_isField p (MulEquiv.isField hfieldQ (quotQpEquiv p).symm.toMulEquiv)

end PadicEval

end RequestProject
