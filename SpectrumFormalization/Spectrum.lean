import SpectrumFormalization.ModP

/-!
# The three classes of prime ideals and the trichotomy of maximal ideals

We introduce the element `z ∈ ℛ_ℝ`, the constant-term homomorphism
`ev₀ : ℛ_ℝ → ℤ`, and the prime-ideal classes of the sequel. We then prove the
**trichotomy of maximal ideals** (Proposition): every maximal ideal `M` of `ℛ_ℝ`
either contains `z` (type (i)), or contains no nonzero integer and not `z`
(type (iii)); the intermediate "type (ii)" (containing an integer `|n|>1` but not
`z`) cannot occur.
-/

open Complex Weierstrass PowerSeries

namespace RequestProject

/-! ## The element `z` and the constant-term homomorphism -/

/-- The coordinate function `z` as an element of `ℛ_ℝ`. -/
noncomputable def zElt : RRsub :=
  mkIntSeq (fun n => if n = 1 then 1 else 0) 1 (by
    intro n
    by_cases h : n = 1 <;> simp [h])

@[simp] theorem intCoeff_zElt (n : ℕ) :
    intCoeff zElt n = if n = 1 then 1 else 0 :=
  intCoeff_mkIntSeq _ _ _ n

/-- The constant-term ring homomorphism `ev₀ : ℛ_ℝ → ℤ`. -/
noncomputable def ev0RR : RRsub →+* ℤ :=
  (PowerSeries.constantCoeff (R := ℤ)).comp coeffHom

theorem ev0RR_eq (x : RRsub) : ev0RR x = intCoeff x 0 := by
  simp [ev0RR, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

@[simp] theorem ev0RR_zElt : ev0RR zElt = 0 := by
  rw [ev0RR_eq, intCoeff_zElt]; rfl

@[simp] theorem ev0RR_natCast (n : ℕ) : ev0RR (n : RRsub) = n := by
  rw [map_natCast]

@[simp] theorem ev0RR_intCast (n : ℤ) : ev0RR (n : RRsub) = n := by
  rw [map_intCast, Int.cast_id]

theorem redHom_zElt (p : ℕ) [Fact p.Prime] : redHom p zElt = PowerSeries.X := by
  ext n
  rw [coeff_redHom, intCoeff_zElt, PowerSeries.coeff_X]
  rcases eq_or_ne n 1 with h | h <;> simp [h]

/-! ## The trichotomy -/

set_option maxHeartbeats 1000000 in
/-
From a nonzero non-unit integer constant in a prime ideal, some rational
prime constant lies in the ideal (using primeness).
-/
theorem exists_prime_mem (M : Ideal RRsub) [hMp : M.IsPrime] {n : ℤ}
    (hn : 1 < n.natAbs) (hnM : (n : RRsub) ∈ M) :
    ∃ p : ℕ, p.Prime ∧ (p : RRsub) ∈ M := by
  revert n hn hnM;
  intro n hn hnM
  induction' hN : n.natAbs using Nat.strong_induction_on with N ih generalizing n
  obtain ⟨p, hp_prime, hp_div⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ Int.natAbs n := by
    exact Nat.exists_prime_and_dvd hn.ne';
  -- Write $n = p * k$ with $k : ℤ$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, n = p * k := by
    exact Int.natCast_dvd.mpr hp_div;
  -- Since $M$ is prime and $(n:RRsub) = (p:RRsub) * (k:RRsub) ∈ M$, either $(p:RRsub) ∈ M$ or $(k:RRsub) ∈ M$.
  by_cases h_case : (p : RRsub) ∈ M;
  · exact ⟨ p, hp_prime, h_case ⟩;
  · -- Since $k \neq 0$ and $k.natAbs < n.natAbs$, we can apply the induction hypothesis to $k$.
    have hk_ne_zero : k ≠ 0 := by
      aesop_cat
    have hk_lt : k.natAbs < n.natAbs := by
      simp_all +decide [ Int.natAbs_mul ];
      nlinarith [ hp_prime.two_le ]
    have hk_ind : (k : RRsub) ∈ M := by
      have hk_ind : (p : RRsub) * (k : RRsub) ∈ M := by
        convert hnM using 1 ; aesop;
      exact hMp.mem_or_mem hk_ind |> Or.resolve_left <| by simpa using h_case;
    by_cases hk_abs : k.natAbs = 1;
    · rcases Int.natAbs_eq_iff.mp hk_abs with ( rfl | rfl ) <;> simp_all +decide;
    · exact ih _ ( by linarith ) ( lt_of_le_of_ne ( Int.natAbs_pos.mpr hk_ne_zero ) ( Ne.symm hk_abs ) ) hk_ind rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The engine of the trichotomy.** If a rational prime constant `p` lies in a
maximal ideal `M`, then `z ∈ M`. (Via `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`: an element of `M` with
unit constant term would be a unit mod `p`, forcing `1 ∈ M`.) -/
theorem zElt_mem_of_prime_mem (M : Ideal RRsub) (hM : M.IsMaximal) {p : ℕ}
    [Fact p.Prime] (hpM : (p : RRsub) ∈ M) : zElt ∈ M := by
  by_contra hz
  haveI : M.IsMaximal := hM
  have hfield : IsField (RRsub ⧸ M) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient M).mp hM
  -- In the field `ℛ_ℝ⁄M`, `z` is a nonzero element, hence a unit.
  have hzq : Ideal.Quotient.mk M zElt ≠ 0 :=
    fun h => hz (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨u, hu'⟩ := hfield.mul_inv_cancel hzq
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective u
  have hu : Ideal.Quotient.mk M (zElt * w) = Ideal.Quotient.mk M 1 := by
    rw [map_mul, hw, map_one]; exact hu'
  have hmem : zElt * w - 1 ∈ M := Ideal.Quotient.eq.mp hu
  -- `m := 1 - z*w ∈ M`.
  set m : RRsub := 1 - zElt * w with hm_def
  have hmM : m ∈ M := by
    rw [hm_def, ← neg_sub]; exact M.neg_mem hmem
  -- constant term of `m` is `1`.
  have h_ev : ev0RR m = 1 := by
    rw [hm_def, map_sub, map_one, map_mul, ev0RR_zElt, zero_mul, sub_zero]
  -- `redHom p m` is a unit (constant coeff `1`).
  have h_unit : IsUnit (redHom p m) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_redHom, ← ev0RR_eq, h_ev]
    simp
  obtain ⟨ψ, hψ⟩ := h_unit.exists_right_inv
  obtain ⟨v, hv⟩ := redHom_surjective p ψ
  have hmv : m * v - 1 ∈ Ideal.span {(p : RRsub)} := by
    rw [← ker_redHom p, RingHom.mem_ker, map_sub, map_mul, map_one, hv, hψ, sub_self]
  have hmvM : m * v - 1 ∈ M := (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpM)) hmv
  exact hM.ne_top (Ideal.eq_top_iff_one _ |>.mpr
    (by simpa using M.sub_mem (M.mul_mem_right v hmM) hmvM))

/-- **Trichotomy of maximal ideals.** Every maximal ideal `M` of `ℛ_ℝ` either
contains `z` (type (i)), or contains no nonzero integer and not `z` (type (iii)).
The intermediate "type (ii)" — containing an integer `n` with `|n| > 1` but not
`z` — cannot occur. -/
theorem trichotomy (M : Ideal RRsub) (hM : M.IsMaximal) :
    zElt ∈ M ∨ (zElt ∉ M ∧ ∀ n : ℤ, (n : RRsub) ∈ M → n = 0) := by
  haveI : M.IsPrime := hM.isPrime
  by_cases hz : zElt ∈ M
  · exact Or.inl hz
  · refine Or.inr ⟨hz, ?_⟩
    intro n hnM
    by_contra hn0
    -- `n ≠ 0`; it cannot be a unit (else `M = ⊤`), so `|n| > 1`.
    have hnu : ¬ IsUnit (n : RRsub) := fun hu => hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hnM hu)
    have hnat : 1 < n.natAbs := by
      rcases lt_trichotomy n.natAbs 1 with h | h | h
      · interval_cases hh : n.natAbs
        · exact absurd (Int.natAbs_eq_zero.mp hh) hn0
      · rw [Int.natAbs_eq_iff] at h
        rcases h with h | h <;> subst h <;> simp_all
      · exact h
    obtain ⟨p, hp, hpM⟩ := exists_prime_mem M hnat hnM
    haveI : Fact p.Prime := ⟨hp⟩
    exact hz (zElt_mem_of_prime_mem M hM hpM)

end RequestProject