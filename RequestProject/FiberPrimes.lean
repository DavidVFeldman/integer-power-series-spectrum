import RequestProject.ConcreteFiber

/-!
# The fiber of `φ` over the augmentation ideal (Proposition `prop:fiber`, remainder)

This file completes Proposition `prop:fiber` of *Integer Coefficients Power
Series with Prescribed Zero Sets* (Bannon–Feldman), whose "core" — the
isomorphism `ℛ/𝔫₀ ≅ ℤ[i]` (`fiberEquiv`) — is in `RequestProject.ConcreteFiber`.

Two statements remain.

* **Quotient correspondence** (`fiberPrimesEquiv`): the primes of `ℛ = Rsub`
  containing the augmentation ideal `𝔫₀ = augIdeal` biject, order-compatibly,
  with `Spec(ℤ[i])`. This is the ideal correspondence along the surjection
  `ev0R : ℛ → ℤ[i]` with kernel `𝔫₀`.

* **Only `𝔫₀` lies in the image of `φ`** (`phi_fiber`): no prime of `ℛ` strictly
  containing `𝔫₀` is the contraction `𝔪 ∩ ℛ` of a maximal ideal `𝔪` of
  `𝒪(𝔻) = OD`. Concretely we show that a maximal ideal `𝔪` of `𝒪(𝔻)` whose
  contraction contains `𝔫₀` must be the evaluation ideal `𝔪₀ = ker(ev₀)`, whose
  contraction is exactly `𝔫₀`.

The ingredients for the second item are:

* `m0_isMaximal` — `𝔪₀ = ker(ev₀ : 𝒪(𝔻) → ℂ)` is maximal (evaluation at `0` is
  surjective onto the field `ℂ`, via constants);
* `augIdeal_map_eq_m0` — `𝔫₀ · 𝒪(𝔻) = 𝔪₀`, the nontrivial inclusion being
  division by `z` inside `𝒪(𝔻)` (`exists_zOD_factor`, built from `dslope`).
-/

open Complex Weierstrass

namespace RequestProject

/-! ## The quotient correspondence: primes over `𝔫₀` versus `Spec(ℤ[i])` -/

theorem ker_ev0R : RingHom.ker ev0R = augIdeal := rfl

/-- **Quotient correspondence (Proposition `prop:fiber`).** The primes of
`ℛ` containing the augmentation ideal `𝔫₀` correspond, order-isomorphically, to
the primes of `ℤ[i]`. The forward map is `P ↦ P·ℤ[i] = P.map ev0R` and the
inverse is `Q ↦ Q ∩ ℛ = Q.comap ev0R`. -/
noncomputable def fiberPrimesEquiv :
    {P : Ideal Rsub // P.IsPrime ∧ augIdeal ≤ P} ≃o {Q : Ideal GaussianInt // Q.IsPrime} where
  toFun P :=
    ⟨P.1.map ev0R, by
      haveI : P.1.IsPrime := P.2.1
      exact Ideal.map_isPrime_of_surjective ev0R_surjective (by rw [ker_ev0R]; exact P.2.2)⟩
  invFun Q :=
    ⟨Q.1.comap ev0R, by
      haveI : Q.1.IsPrime := Q.2
      exact ⟨Ideal.comap_isPrime ev0R Q.1, by
        rw [← ker_ev0R]
        exact fun x hx => by simp [RingHom.mem_ker.mp hx]⟩⟩
  left_inv P := by
    apply Subtype.ext
    show Ideal.comap ev0R (Ideal.map ev0R P.1) = P.1
    rw [Ideal.comap_map_of_surjective ev0R ev0R_surjective]
    exact sup_eq_left.mpr (by simpa [← ker_ev0R] using P.2.2)
  right_inv Q := by
    apply Subtype.ext
    exact Ideal.map_comap_of_surjective ev0R ev0R_surjective Q.1
  map_rel_iff' {P P'} := by
    refine ⟨fun h => ?_, fun h => Ideal.map_mono h⟩
    have h1 : P.1 ≤ Ideal.comap ev0R (Ideal.map ev0R P'.1) :=
      Ideal.map_le_iff_le_comap.mp h
    rw [Ideal.comap_map_of_surjective ev0R ev0R_surjective] at h1
    refine h1.trans ?_
    exact sup_le le_rfl (by simpa [← ker_ev0R] using P'.2.2)

theorem fiberPrimesEquiv_apply (P : {P : Ideal Rsub // P.IsPrime ∧ augIdeal ≤ P}) :
    (fiberPrimesEquiv P : Ideal GaussianInt) = P.1.map ev0R := rfl

theorem fiberPrimesEquiv_symm_apply (Q : {Q : Ideal GaussianInt // Q.IsPrime}) :
    (fiberPrimesEquiv.symm Q : Ideal Rsub) = Q.1.comap ev0R := rfl

/-! ## The evaluation ideal `𝔪₀` of `𝒪(𝔻)` -/

/-- The maximal ideal `𝔪₀ = ker(ev₀)` of `𝒪(𝔻)` of functions vanishing at `0`. -/
noncomputable def m0 : Ideal OD := RingHom.ker ODeval0

theorem mem_m0 {F : OD} : F ∈ m0 ↔ ODeval0 F = 0 := Iff.rfl

/-- Evaluation at `0` is surjective from `𝒪(𝔻)` onto `ℂ` (constants). -/
theorem ODeval0_surjective : Function.Surjective ODeval0 := by
  intro c
  exact ⟨ODmk ⟨fun _ => c, analyticOnNhd_const⟩, rfl⟩

/-- **`𝔪₀` is maximal**, since `𝒪(𝔻)/𝔪₀ ≅ ℂ`. -/
theorem m0_isMaximal : m0.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective ODeval0 ODeval0_surjective

/-! ## The coordinate function inside `ℛ` -/

theorem analyticOnNhd_coord : AnalyticOnNhd ℂ (fun z : ℂ => z) 𝔻 :=
  fun _ _ => analyticAt_id

/-- The coordinate function `z` as an element of `ℛ`. -/
noncomputable def zR : Rsub :=
  ⟨ODmk ⟨fun z : ℂ => z, analyticOnNhd_coord⟩, by
    refine ⟨⟨fun z : ℂ => z, analyticOnNhd_coord⟩, ?_, rfl⟩
    intro m
    rw [taylorCoeff_id]
    by_cases h : m = 1
    · simp only [h, if_true]; exact GaussianInt.toComplex.range.one_mem
    · simp only [h, if_false]; exact GaussianInt.toComplex.range.zero_mem⟩

theorem zR_mem_augIdeal : zR ∈ augIdeal := by
  rw [mem_augIdeal]
  rfl

/-- **Division by `z` in `𝒪(𝔻)`.** A holomorphic function on `𝔻` vanishing at
`0` is `z` times a holomorphic function on `𝔻`. -/
theorem exists_zOD_factor (F : OD) (h : ODeval0 F = 0) :
    ∃ G : OD, F = Rsub.subtype zR * G := by
  obtain ⟨f, rfl⟩ := ODmk.surjective F
  have hf0 : (f : ℂ → ℂ) 0 = 0 := h
  have hdiff : DifferentiableOn ℂ (f : ℂ → ℂ) (Metric.ball 0 1) :=
    f.2.differentiableOn.mono (by simp +decide [Metric.ball])
  have hu : AnalyticOnNhd ℂ (dslope (f : ℂ → ℂ) 0) 𝔻 :=
    (((differentiableOn_dslope (Metric.ball_mem_nhds 0 zero_lt_one)).mpr
      hdiff).analyticOnNhd Metric.isOpen_ball)
  refine ⟨ODmk ⟨dslope (f : ℂ → ℂ) 0, hu⟩, ?_⟩
  show ODmk f = ODmk ⟨fun z : ℂ => z, analyticOnNhd_coord⟩ * ODmk ⟨dslope (f : ℂ → ℂ) 0, hu⟩
  rw [← map_mul]
  refine ODmk_eq_iff.mpr fun z _ => ?_
  have := sub_smul_dslope (f : ℂ → ℂ) 0 z
  simp only [sub_zero, smul_eq_mul, hf0, sub_zero] at this
  simpa using this.symm

/-- **`𝔫₀ · 𝒪(𝔻) = 𝔪₀`.** -/
theorem augIdeal_map_eq_m0 : augIdeal.map Rsub.subtype = m0 := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_m0]
    exact (mem_augIdeal x).mp hx
  · intro F hF
    obtain ⟨G, rfl⟩ := exists_zOD_factor F (mem_m0.mp hF)
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ zR_mem_augIdeal)

/-- The contraction of `𝔪₀` to `ℛ` is the augmentation ideal `𝔫₀`. -/
theorem comap_m0 : m0.comap Rsub.subtype = augIdeal := by
  ext x
  rw [Ideal.mem_comap, mem_m0, mem_augIdeal]

/-- **Only `𝔫₀` lies in the image of `φ`.** If a maximal ideal `𝔪` of `𝒪(𝔻)`
has `𝔫₀ ≤ 𝔪 ∩ ℛ`, then `𝔪 = 𝔪₀` and hence `𝔪 ∩ ℛ = 𝔫₀`. Consequently no prime
of `ℛ` *strictly* containing `𝔫₀` is a contraction of a maximal ideal of
`𝒪(𝔻)`. -/
theorem phi_fiber (m : Ideal OD) (hm : m.IsMaximal)
    (h : augIdeal ≤ m.comap Rsub.subtype) :
    m = m0 ∧ m.comap Rsub.subtype = augIdeal := by
  have hle : m0 ≤ m := by
    rw [← augIdeal_map_eq_m0, Ideal.map_le_iff_le_comap]
    exact h
  have hmeq : m = m0 := ((m0_isMaximal.eq_of_le hm.ne_top hle)).symm
  exact ⟨hmeq, by rw [hmeq, comap_m0]⟩

/-- Restatement of `phi_fiber`: a prime of `ℛ` that strictly contains `𝔫₀` is
not the contraction of any maximal ideal of `𝒪(𝔻)`. -/
theorem not_comap_of_augIdeal_lt (P : Ideal Rsub) (hP : augIdeal < P) :
    ¬ ∃ m : Ideal OD, m.IsMaximal ∧ m.comap Rsub.subtype = P := by
  rintro ⟨m, hm, rfl⟩
  exact absurd (phi_fiber m hm hP.le).2 hP.ne'

end RequestProject
