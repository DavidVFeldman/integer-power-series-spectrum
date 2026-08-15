import SpectrumFormalization.CoeffHom

/-!
# Reduction mod `p`: `ℛ_ℝ/(p) ≅ 𝔽ₚ⟦z⟧`

For a rational prime `p`, reducing the integer coefficient homomorphism modulo
`p` gives a **surjective** ring homomorphism `redHom p : ℛ_ℝ → 𝔽ₚ⟦z⟧` whose kernel
is the ideal `(p)`. This is the key structural input for the trichotomy of
maximal ideals and the classification of primes outside `𝔓₁`.
-/

open Complex Weierstrass PowerSeries

namespace RequestProject

/-! ## An element of `ℛ_ℝ` from a bounded integer sequence -/

/-- The element of `ℛ_ℝ` realized by a bounded integer coefficient sequence. -/
noncomputable def mkIntSeq (c : ℕ → ℤ) (C : ℝ) (hC : ∀ n, ‖(c n : ℂ)‖ ≤ C) : RRsub :=
  ⟨ODmk ⟨psFun (fun n => (c n : ℂ)), psFun_analyticOnNhd hC⟩, by
    refine ⟨⟨psFun (fun n => (c n : ℂ)), psFun_analyticOnNhd hC⟩, ?_, rfl⟩
    intro m
    rw [psFun_taylorCoeff hC m]
    exact ⟨c m, rfl⟩⟩

theorem intCoeff_mkIntSeq (c : ℕ → ℤ) (C : ℝ) (hC : ∀ n, ‖(c n : ℂ)‖ ≤ C) (n : ℕ) :
    intCoeff (mkIntSeq c C hC) n = c n := by
  have h : (intCoeff (mkIntSeq c C hC) n : ℂ) = (c n : ℂ) := by
    rw [intCoeff_spec]
    show ODtaylorCoeff (ODmk ⟨psFun (fun n => (c n : ℂ)), _⟩) n = (c n : ℂ)
    rw [ODtaylorCoeff_mk]
    exact psFun_taylorCoeff hC n
  exact_mod_cast h

/-! ## The reduction homomorphism -/

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Reduction mod `p`.** The coefficientwise reduction `ℛ_ℝ → 𝔽ₚ⟦z⟧`. -/
noncomputable def redHom : RRsub →+* PowerSeries (ZMod p) :=
  (PowerSeries.map (Int.castRingHom (ZMod p))).comp coeffHom

@[simp] theorem coeff_redHom (x : RRsub) (n : ℕ) :
    PowerSeries.coeff (R := ZMod p) n (redHom p x) = (intCoeff x n : ZMod p) := by
  simp [redHom, PowerSeries.coeff_map]

theorem constantCoeff_redHom (x : RRsub) :
    constantCoeff (redHom p x) = (intCoeff x 0 : ZMod p) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_redHom]

/-
`redHom` is surjective: every `𝔽ₚ`-power series lifts to `ℛ_ℝ` via the
bounded `{0,…,p-1}` digit expansion.
-/
theorem redHom_surjective : Function.Surjective (redHom p) := by
  intro ψ;
  use mkIntSeq (fun n => (ψ.coeff n).val) p (fun n => by
    norm_num;
    convert Complex.norm_intCast ( ( ψ.coeff n |> ZMod.val ) : ℤ ) |> ( fun h => h.le.trans ?_ ) using 1;
    · cases p <;> aesop;
    · exact_mod_cast Nat.le_of_lt ( ZMod.val_lt _ ))
  generalize_proofs at *;
  ext n; simp +decide [ coeff_redHom, intCoeff_mkIntSeq ] ;

/-
`p` maps to `0` under `redHom`.
-/
theorem redHom_natCast_p : redHom p (p : RRsub) = 0 := by
  ext n;
  simp +decide [ redHom, intCoeff ];
  erw [ PowerSeries.coeff_C ] ; aesop

/-
**The kernel of `redHom` is `(p)`.**
-/
theorem ker_redHom : RingHom.ker (redHom p) = Ideal.span {(p : RRsub)} := by
  refine' le_antisymm _ _;
  · intro x hx;
    -- By definition of $redHom$, we know that for all $n$, $(intCoeff x n : ZMod p) = 0$.
    have h_coeff_zero : ∀ n, (intCoeff x n : ZMod p) = 0 := by
      intro n; replace hx := congr_arg ( fun f => PowerSeries.coeff ( R := ZMod p ) n f ) hx; aesop;
    -- Since $p \mid intCoeff x n$ for all $n$, we can write $intCoeff x n = p * k_n$ for some integer $k_n$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ → ℤ, ∀ n, intCoeff x n = p * k n := by
      exact ⟨ fun n => ( intCoeff x n ) / p, fun n => by rw [ mul_comm, Int.ediv_mul_cancel ( by simpa [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] using h_coeff_zero n ) ] ⟩;
    -- Define the function $g : ℂ → ℂ$ by $g(z) = \frac{1}{p} f(z)$.
    obtain ⟨f, hf⟩ : ∃ f : diskAnalytic, IsIntegerCoeffs (f : ℂ → ℂ) ∧ ODmk f = RRsub.subtype x := by
      exact mem_RRsub.mp x.2
    generalize_proofs at *;
    -- Define the function $g : ℂ → ℂ$ by $g(z) = \frac{1}{p} f(z)$ and show that it has integer coefficients.
    obtain ⟨g, hg⟩ : ∃ g : diskAnalytic, IsIntegerCoeffs (g : ℂ → ℂ) ∧ ∀ z ∈ 𝔻, (g : ℂ → ℂ) z = (p : ℂ)⁻¹ * (f : ℂ → ℂ) z := by
      refine' ⟨ ⟨ fun z => ( p : ℂ ) ⁻¹ * ( f : ℂ → ℂ ) z, _ ⟩, _, _ ⟩ <;> simp_all +decide [ IsIntegerCoeffs ];
      · exact AnalyticOnNhd.mul ( analyticOnNhd_const ) f.2;
      · intro n
        have h_coeff : taylorCoeff (fun z => (p : ℂ)⁻¹ * (f : ℂ → ℂ) z) n = (p : ℂ)⁻¹ * taylorCoeff (f : ℂ → ℂ) n := by
          unfold taylorCoeff; simp +decide [ iteratedDeriv_const_mul ] ;
          ring
        generalize_proofs at *;
        have h_coeff : taylorCoeff (f : ℂ → ℂ) n = intCoeff x n := by
          rw [ intCoeff_spec ];
          rw [ ← hf.2, ODtaylorCoeff_mk ]
        generalize_proofs at *;
        simp_all +decide [ mul_assoc, mul_left_comm, mul_comm ]
    generalize_proofs at *;
    -- Show that $x = p \cdot g$.
    have h_eq : RRsub.subtype x = (p : OD) * ODmk g := by
      rw [ ← hf.2 ];
      refine' ODmk_eq_iff.mpr _;
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, hp.1.ne_zero ]
    generalize_proofs at *;
    rw [ Ideal.mem_span_singleton' ];
    use ⟨ODmk g, by
      exact ⟨ g, hg.1, rfl ⟩⟩
    generalize_proofs at *;
    exact Subtype.ext <| by simpa [ mul_comm ] using h_eq.symm;
  · exact Ideal.span_le.mpr ( by simp +decide [ redHom_natCast_p p ] )

end RequestProject