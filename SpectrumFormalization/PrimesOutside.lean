import SpectrumFormalization.DomainFacts

/-!
# Prime ideals outside `𝔓₁`

This file formalizes results on prime ideals of `ℛ_ℝ` that lie **outside** the
class `𝔓₁` (Proposition *Prime ideals outside `𝔓₁`* of the paper *Integer
Coefficients Power Series with Prescribed Zero Sets*, v19):

* the constant ideals `(p)` (`p` a rational prime) are **prime but not maximal**;
* the ideals `(z, p)` are **maximal**;
* the zero ideal `(0)` and `(z)` are prime;
* **complete classification of primes containing `z`**: a prime `P` with `z ∈ P`
  is either `(z)` or `(z, p)` for a rational prime `p`; consequently the
  **type-(i) maximal ideals are exactly the `(z, p)`**;
* a prime `P` with `z ∉ P` that contains a rational prime `p` equals `(p)`;
* **the converse direction**: a prime `P` with `z ∉ P` meeting `ℤ` nontrivially
  contains a rational prime (`prime_contains_rat_prime`) and hence equals `(p)`
  (`classify_prime_of_z_not_mem`), giving the corrected trichotomy
  `spec_trichotomy` on `Spec(ℛ_ℝ)`.

The engine is the identification `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧` from `ModP.lean`
(`redHom`, `redHom_surjective`, `ker_redHom`), the identification
`ℛ_ℝ/(z) ≅ ℤ` (`ker_ev0RR`) and the correspondence theorem, together with
division by `z` (`exists_zElt_factor`).

*Remark on the paper.* The paper's Proposition claims every prime outside `𝔓₁`
is `(p)` or `(z, p)`; this **omits** the primes `(0)` and `(z)`, which are
genuine primes outside `𝔓₁` (added here). The paper's argument for the converse
direction (that the image of `P` in `𝔽ₚ⟦z⟧` is prime) is not justified, since
that image need not be a prime ideal; it is **superseded** here by the direct
factorization argument `prime_contains_rat_prime`, which yields
`classify_prime_of_z_not_mem`. Note that the converse holds with the hypothesis
`P ∩ ℤ ≠ 0`, not merely `P ≠ (0)`: any point-evaluation ideal `P_a` with `a ≠ 0`
is a nonzero prime with `z ∉ P_a` that is not of the form `(p)`.
-/

open Complex Weierstrass PowerSeries

namespace RequestProject

/-- `𝔓₁`: `P` contains at least one element with unit constant term
(i.e. an element `1 + zF`, up to sign). -/
def IsInP1 (P : Ideal RRsub) : Prop := ∃ f ∈ P, IsUnit (ev0RR f)

/-! ## The quotient `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧` -/

/-- The ring isomorphism `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`. -/
noncomputable def quotSpanPEquiv (p : ℕ) [Fact p.Prime] :
    (RRsub ⧸ Ideal.span {(p : RRsub)}) ≃+* PowerSeries (ZMod p) :=
  (Ideal.quotEquivOfEq (ker_redHom p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (redHom_surjective p))

/-! ## `(p)` is prime but not maximal -/

/-
The constant ideal `(p)` is **prime**.
-/
theorem span_p_isPrime (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : RRsub)}).IsPrime := by
  -- Since $p$ is prime, the ideal $(p)$ in $\mathbb{Z}$ is prime.
  have h_prime : Ideal.IsPrime (Ideal.span {(p : ℤ)}) := by
    rw [ Ideal.span_singleton_prime ];
    · exact Nat.prime_iff_prime_int.mp Fact.out;
    · exact mod_cast Nat.Prime.ne_zero Fact.out;
  have h_red_prime : Ideal.IsPrime (RingHom.ker (redHom p)) := by
    convert Ideal.isPrime_iff.mpr _;
    simp +decide [ Ideal.eq_top_iff_one, redHom ];
  rwa [ ker_redHom ] at h_red_prime

/-
The constant ideal `(p)` is **not maximal** (its quotient `𝔽ₚ⟦z⟧` is not a
field: `z` is not invertible).
-/
theorem span_p_not_isMaximal (p : ℕ) [Fact p.Prime] :
    ¬ (Ideal.span {(p : RRsub)}).IsMaximal := by
  intro h_maximal;
  have h_field : IsField (RRsub ⧸ Ideal.span {(p : RRsub)}) := by
    exact @Field.toIsField _ ( Ideal.Quotient.field _ );
  have h_field : IsField (PowerSeries (ZMod p)) := by
    refine' { .. };
    · exact ⟨ 0, 1, by have := h_field.exists_pair_ne; aesop ⟩;
    · exact fun x y => mul_comm x y;
    · intro a ha
      obtain ⟨b, hb⟩ : ∃ b : RRsub ⧸ Ideal.span {(p : RRsub)}, (quotSpanPEquiv p).symm a * b = 1 := by
        exact h_field.mul_inv_cancel ( by simpa [ quotSpanPEquiv ] using ha );
      exact ⟨ quotSpanPEquiv p b, by simpa using congr_arg ( quotSpanPEquiv p ) hb ⟩;
  obtain ⟨ u, hu ⟩ := h_field.mul_inv_cancel ( show ( PowerSeries.X : PowerSeries ( ZMod p ) ) ≠ 0 from PowerSeries.X_ne_zero );
  apply_fun PowerSeries.constantCoeff at hu ; simp_all +decide

/-! ## `(z, p)` is maximal -/

/-- The constant-term-mod-`p` homomorphism `ℛ_ℝ → 𝔽ₚ`. -/
noncomputable def evZP (p : ℕ) [Fact p.Prime] : RRsub →+* ZMod p :=
  (Int.castRingHom (ZMod p)).comp ev0RR

theorem evZP_surjective (p : ℕ) [Fact p.Prime] : Function.Surjective (evZP p) :=
  ZMod.ringHom_surjective (evZP p)

theorem ker_evZP (p : ℕ) [Fact p.Prime] :
    RingHom.ker (evZP p) = Ideal.span {zElt, (p : RRsub)} := by
  refine' le_antisymm _ _ <;> intro x hx <;> simp_all +decide [ Ideal.mem_span_singleton, RingHom.mem_ker ];
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, ev0RR x = p * m := by
      exact exists_eq_mul_right_of_dvd <| by rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
    obtain ⟨y, hy⟩ : ∃ y : RRsub, x - (p : RRsub) * (m : RRsub) = zElt * y := by
      convert exists_zElt_factor ( x - ( p : RRsub ) * ( m : RRsub ) ) _ using 1;
      simp +decide [ hm, map_mul, map_sub ];
    rw [ sub_eq_iff_eq_add ] at hy;
    exact hy.symm ▸ Ideal.add_mem _ ( Ideal.mul_mem_right _ _ ( Ideal.subset_span ( Set.mem_insert _ _ ) ) ) ( Ideal.mul_mem_right _ _ ( Ideal.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) );
  · rw [ Ideal.mem_span_pair ] at hx;
    obtain ⟨ a, b, rfl ⟩ := hx; simp +decide [ evZP ] ;

/-
The ideal `(z, p)` is **maximal**, with `ℛ_ℝ/(z,p) ≅ 𝔽ₚ`.
-/
theorem span_zp_isMaximal (p : ℕ) [Fact p.Prime] :
    (Ideal.span {zElt, (p : RRsub)}).IsMaximal := by
  rw [← ker_evZP p]
  have e : (RRsub ⧸ RingHom.ker (evZP p)) ≃+* ZMod p :=
    RingHom.quotientKerEquivOfSurjective (evZP_surjective p)
  have hfield : IsField (RRsub ⧸ RingHom.ker (evZP p)) :=
    MulEquiv.isField (Field.toIsField (ZMod p)) e.toMulEquiv
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfield

/-! ## `(0)` and `(z)` are prime -/

/-- The zero ideal `(0)` is prime (`ℛ_ℝ` is a domain). -/
theorem bot_isPrime : (⊥ : Ideal RRsub).IsPrime := Ideal.isPrime_bot

/-
The constant-term homomorphism `ev₀ : ℛ_ℝ → ℤ` is surjective.
-/
theorem ev0RR_surjective : Function.Surjective ev0RR := by
  intro n;
  exact ⟨ n, by aesop ⟩

/-
The ideal `(z)` is prime (`ℛ_ℝ/(z) ≅ ℤ`).
-/
theorem span_zElt_isPrime : (Ideal.span {zElt}).IsPrime := by
  rw [← ker_ev0RR]; exact RingHom.ker_isPrime ev0RR

/-! ## Prime ideals of `ℤ` -/

/-
Every prime ideal of `ℤ` is `(0)` or `(p)` for a rational prime `p`.
-/
theorem int_prime_ideal (Q : Ideal ℤ) [Q.IsPrime] :
    Q = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ Q = Ideal.span {(p : ℤ)} := by
  by_cases hQ : Q = ⊥ <;> simp_all +decide [ Ideal.span_singleton_eq_bot ];
  -- Since $Q$ is a nonzero prime ideal of $\mathbb{Z}$, it must be of the form $(p)$ for some prime $p$.
  obtain ⟨p, hp⟩ : ∃ p : ℕ, Q = Ideal.span {(p : ℤ)} := by
    obtain ⟨ p, hp ⟩ := IsPrincipalIdealRing.principal Q; use p.natAbs; simp_all +decide [ abs_of_nonneg ] ;
  simp_all +decide [ Ideal.span_singleton_prime ];
  exact ⟨ p, Nat.prime_iff_prime_int.mpr ‹_›, rfl ⟩

/-! ## Classification of primes containing `z` -/

/-
`comap` of `(p) ⊆ ℤ` along `ev₀` is `(z, p)`.
-/
theorem comap_ev0RR_span_int (p : ℕ) [Fact p.Prime] :
    Ideal.comap ev0RR (Ideal.span {(p : ℤ)}) = Ideal.span {zElt, (p : RRsub)} := by
  convert ker_evZP p using 1;
  ext; simp [evZP];
  rw [ Ideal.mem_span_singleton ];
  erw [ ZMod.intCast_zmod_eq_zero_iff_dvd ]

/-
**Classification of primes containing `z`.** A prime ideal `P` of `ℛ_ℝ` with
`z ∈ P` is either `(z)` or `(z, p)` for a rational prime `p`.
-/
theorem prime_of_z_mem (P : Ideal RRsub) [hP : P.IsPrime] (hz : zElt ∈ P) :
    P = Ideal.span {zElt} ∨
    (∃ p : ℕ, p.Prime ∧ P = Ideal.span {zElt, (p : RRsub)}) := by
  -- By `int_prime_ideal Q`, there are two cases for `Q = Ideal.map ev0RR P`.
  obtain (hQ | ⟨p, hp, hQ⟩) : Ideal.map ev0RR P = ⊥ ∨ ∃ p : ℕ, p.Prime ∧ Ideal.map ev0RR P = Ideal.span {(p : ℤ)} := by
    convert int_prime_ideal ( Ideal.map ev0RR P ) using 1;
    apply_rules [ Ideal.map_isPrime_of_surjective, ev0RR_surjective ];
    exact fun x hx => by rw [ ker_ev0RR ] at hx; exact Ideal.span_le.mpr ( by aesop ) hx;
  · -- If `Ideal.map ev0RR P = ⊥`, then `P` is contained in the kernel of `ev0RR`.
    have hP_subset_ker : P ≤ RingHom.ker ev0RR := by
      exact fun x hx => by simpa using Ideal.mem_bot.mp ( hQ ▸ Ideal.mem_map_of_mem _ hx ) ;
    exact Or.inl <| le_antisymm ( hP_subset_ker.trans <| by simp +decide [ ker_ev0RR ] ) <| Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr hz;
  · have hP_eq : P = Ideal.comap ev0RR (Ideal.span {(p : ℤ)}) := by
      rw [ ← hQ, Ideal.comap_map_of_surjective ev0RR ev0RR_surjective ];
      simp +decide [ ker_ev0RR ];
      exact fun x hx => by rw [ show Ideal.comap ev0RR ⊥ = Ideal.span { zElt } from ker_ev0RR ] at hx; exact Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hz ) hx;
    refine Or.inr ⟨ p, hp, ?_ ⟩;
    convert comap_ev0RR_span_int p using 1;
    exact ⟨ hp ⟩

/-
**Type-(i) maximal ideals are exactly the `(z, p)`.** A maximal ideal `M`
contains `z` iff `M = (z, p)` for a rational prime `p`.
-/
theorem typeI_maximal_iff (M : Ideal RRsub) (hM : M.IsMaximal) :
    zElt ∈ M ↔ ∃ p : ℕ, p.Prime ∧ M = Ideal.span {zElt, (p : RRsub)} := by
  refine' ⟨ fun hz => _, fun ⟨ p, hp, hM' ⟩ => hM'.symm ▸ Ideal.subset_span ( by simp +decide ) ⟩;
  obtain h | ⟨ p, hp, rfl ⟩ := prime_of_z_mem M hz;
  · contrapose! hM;
    intro H;
    have h_contra : IsField (RRsub ⧸ RingHom.ker ev0RR) := by
      convert Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.1 H; all_goals rw [ h, ker_ev0RR ];
    have h_contra : IsField ℤ := by
      convert h_contra;
      have h_contra : RingEquiv (RRsub ⧸ RingHom.ker ev0RR) ℤ := by
        exact RingHom.quotientKerEquivOfSurjective ( ev0RR_surjective );
      constructor <;> intro h <;> have := h_contra.symm;
      · finiteness;
      · convert h_contra.symm.isField h;
    exact absurd ( h_contra.mul_inv_cancel ( show ( 2 : ℤ ) ≠ 0 by decide ) ) ( by rintro ⟨ x, hx ⟩ ; linarith [ show x = 0 by linarith ] );
  · use p

/-! ## A prime not containing `z` but containing a prime `p` is `(p)` -/

/-
In `K⟦X⟧` for a field `K` (a DVR), a prime ideal not containing `X` is `(0)`.
-/
theorem powerSeries_field_prime_eq_bot_of_X_not_mem {K : Type*} [Field K]
    (Q : Ideal (PowerSeries K)) [hQ : Q.IsPrime] (hX : PowerSeries.X ∉ Q) : Q = ⊥ := by
  refine' eq_bot_iff.mpr fun f hf => _;
  by_cases hf0 : f = 0;
  · exact hf0.symm ▸ Submodule.zero_mem _;
  · -- Let $n = f.order.toNat$ and $u = f.divXPowOrder$. Since $u$ is a unit and $f = X^n * u \in Q$, we get $X^n \in Q$.
    obtain ⟨n, u, hu⟩ : ∃ n : ℕ, ∃ u : K⟦X⟧, f = PowerSeries.X ^ n * u ∧ IsUnit u := by
      use f.order.toNat, f.divXPowOrder;
      exact ⟨ by rw [ PowerSeries.X_pow_order_mul_divXPowOrder ], PowerSeries.isUnit_divided_by_X_pow_order hf0 ⟩;
    have hXn : PowerSeries.X ^ n ∈ Q := by
      obtain ⟨ v, hv ⟩ := hu.2.exists_left_inv; have := Q.mul_mem_left v hf; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    exact False.elim ( hX ( hQ.mem_of_pow_mem n hXn ) )

/-
**A prime `P` with `z ∉ P` containing a rational prime `p` equals `(p)`.**
(Via `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`, a DVR whose only prime not containing `z` is `(0)`.)
-/
theorem eq_span_p_of_prime_mem (P : Ideal RRsub) [hP : P.IsPrime] (hz : zElt ∉ P)
    {p : ℕ} [Fact p.Prime] (hp : (p : RRsub) ∈ P) :
    P = Ideal.span {(p : RRsub)} := by
  -- By `Ideal.map_isPrime_of_surjective (redHom_surjective p)` (using `ker (redHom p) ≤ P`), `Q` is prime.
  set Q := Ideal.map (redHom p) P
  have hQ_prime : Q.IsPrime := by
    apply Ideal.map_isPrime_of_surjective (redHom_surjective p);
    rw [ ker_redHom ];
    exact Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hp );
  -- By `powerSeries_field_prime_eq_bot_of_X_not_mem Q (X ∉ Q)`, `Q = ⊥`.
  have hQ_bot : Q = ⊥ := by
    apply powerSeries_field_prime_eq_bot_of_X_not_mem;
    intro hX_in_Q
    have hz_in_P : zElt ∈ P := by
      obtain ⟨ x, hx, hx' ⟩ := Ideal.mem_map_iff_of_surjective ( redHom p ) ( redHom_surjective p ) |>.1 hX_in_Q;
      have hz_in_P : zElt - x ∈ RingHom.ker (redHom p) := by
        simp +decide [ hx', redHom_zElt ];
      rw [ ker_redHom ] at hz_in_P;
      simpa using P.add_mem hx ( Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hp ) hz_in_P )
    contradiction;
  -- Hence `Ideal.map (redHom p) P = ⊥`, so `P ≤ Ideal.comap (redHom p) (Ideal.map (redHom p) P) = Ideal.comap (redHom p) ⊥ = RingHom.ker (redHom p) = Ideal.span {(p:RRsub)}`.
  have hP_le_span : P ≤ Ideal.span {(p : RRsub)} := by
    have hP_le_span : P ≤ RingHom.ker (redHom p) := by
      exact fun x hx => by rw [ RingHom.mem_ker ] ; exact Ideal.mem_bot.mp ( hQ_bot ▸ Ideal.mem_map_of_mem _ hx ) ;
    exact hP_le_span.trans ( by rw [ ker_redHom ] );
  exact le_antisymm hP_le_span ( Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hp ) )

/-! ## The converse: a prime meeting `ℤ` nontrivially contains a rational prime -/

/-- **W4.1.** If a prime ideal `P` of `ℛ_ℝ` contains a nonzero rational integer,
then it contains a rational prime. (Factor `n` in `ℤ`; the image of the
factorization lies in `P`, so `P` contains one of the prime factors. The units
`±1` cannot lie in `P`.) -/
theorem prime_contains_rat_prime (P : Ideal RRsub) [hP : P.IsPrime] {n : ℤ}
    (hn0 : n ≠ 0) (hnP : (n : RRsub) ∈ P) :
    ∃ p : ℕ, p.Prime ∧ (p : RRsub) ∈ P := by
  have hnat : 1 < n.natAbs := by
    rcases lt_trichotomy n.natAbs 1 with h | h | h
    · interval_cases hh : n.natAbs
      · exact absurd (Int.natAbs_eq_zero.mp hh) hn0
    · -- `n = ±1` is a unit, so `P = ⊤`, contradicting primeness.
      exfalso
      have hu : IsUnit ((n : RRsub)) := by
        rcases Int.natAbs_eq_iff.mp h with h' | h' <;> subst h' <;> simp
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hnP hu)
    · exact h
  exact exists_prime_mem P hnat hnP

/-- **W4.2.** A prime ideal `P` of `ℛ_ℝ` with `z ∉ P` that meets `ℤ` nontrivially
is the constant ideal `(p)` for a rational prime `p`.

This is the converse direction of the paper's classification of primes outside
`𝔓₁`; the paper's `𝔽ₚ⟦z⟧`-image argument is replaced by the direct
factorization argument of `prime_contains_rat_prime`. -/
theorem classify_prime_of_z_not_mem (P : Ideal RRsub) [hP : P.IsPrime]
    (hz : zElt ∉ P) {n : ℤ} (hn0 : n ≠ 0) (hnP : (n : RRsub) ∈ P) :
    ∃ p : ℕ, p.Prime ∧ P = Ideal.span {(p : RRsub)} := by
  obtain ⟨p, hp, hpP⟩ := prime_contains_rat_prime P hn0 hnP
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨p, hp, eq_span_p_of_prime_mem P hz hpP⟩

/-- **Corrected trichotomy on `Spec(ℛ_ℝ)`.** Every prime ideal `P` of `ℛ_ℝ`
falls into exactly one of three classes:

(a) `z ∈ P`, and then `P = (z)` or `P = (z, p)` for a rational prime `p`;
(b) `z ∉ P` and `P` contains a nonzero integer, and then `P = (p)` for a rational
    prime `p`;
(c) `z ∉ P` and `P ∩ ℤ = 0`, i.e. `P ∈ 𝔓₁` (this class contains `(0)` and the
    point-evaluation ideals `P_a`).

The three cases are mutually exclusive since their defining conditions are. -/
theorem spec_trichotomy (P : Ideal RRsub) [hP : P.IsPrime] :
    (zElt ∈ P ∧ (P = Ideal.span {zElt} ∨
        ∃ p : ℕ, p.Prime ∧ P = Ideal.span {zElt, (p : RRsub)})) ∨
    (zElt ∉ P ∧ (∃ n : ℤ, n ≠ 0 ∧ (n : RRsub) ∈ P) ∧
        ∃ p : ℕ, p.Prime ∧ P = Ideal.span {(p : RRsub)}) ∨
    (zElt ∉ P ∧ ∀ n : ℤ, (n : RRsub) ∈ P → n = 0) := by
  by_cases hz : zElt ∈ P
  · exact Or.inl ⟨hz, prime_of_z_mem P hz⟩
  · by_cases hint : ∀ n : ℤ, (n : RRsub) ∈ P → n = 0
    · exact Or.inr (Or.inr ⟨hz, hint⟩)
    · push_neg at hint
      obtain ⟨n, hnP, hn0⟩ := hint
      exact Or.inr (Or.inl ⟨hz, ⟨n, hn0, hnP⟩,
        classify_prime_of_z_not_mem P hz hn0 hnP⟩)

end RequestProject