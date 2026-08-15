import SpectrumFormalization.PrimesOutside

/-!
# Type-(iii) maximal ideals contain an element of constant term `1`

This file formalizes part (i) of the sequel's `prop:interesting`: a **type-(iii)**
maximal ideal `M` of `ℛ_ℝ` — one with `z ∉ M` and `M ∩ ℤ = 0` — contains an
element of constant term `1`; equivalently `M ∈ 𝔓₁`.

*On the proof.* The printed argument for the case `d > 1` (embedding a field into
`ℤ/(d)`) is shaky. We formalize instead the following direct argument. Let

`I := ev₀(M) ⊆ ℤ`

which is an ideal of `ℤ` (`constTermImage`), because `ℤ ⊆ ℛ_ℝ` as constants and
`M` absorbs multiplication by them. Suppose `1 ∉ I`, i.e. `I ≠ ⊤`. Choose a
maximal ideal `Q` of `ℤ` containing `I`. By the classification of prime ideals of
`ℤ` there are two cases.

* `Q = (0)`: then `I = 0`, so every element of `M` has constant term `0`, i.e.
  `M ≤ ker ev₀ = (z)`. Since `(z)` is proper and `M` is maximal, `M = (z)`, which
  contains `z` — contradicting `z ∉ M`.
* `Q = (p)` for a rational prime `p`: then `M ≤ ev₀⁻¹(p) = (z, p)` (by
  `comap_ev0RR_span_int`), a proper (indeed maximal) ideal, so again maximality
  gives `M = (z, p) ∋ z`, contradicting `z ∉ M`.

Hence `1 ∈ I`, which is the assertion.

Note that this argument uses only `M` maximal and `z ∉ M`; the hypothesis
`M ∩ ℤ = 0` is part of the statement of "type (iii)" as the paper phrases it, but
is in fact automatic from the other two by `trichotomy`, so it is carried but
unused. (See `typeIII_contains_one`, which drops it.)
-/

open Complex Weierstrass

namespace RequestProject

/-- The image `ev₀(M) ⊆ ℤ` of an ideal `M` of `ℛ_ℝ` under the constant-term
homomorphism, as an ideal of `ℤ`. -/
def constTermImage (M : Ideal RRsub) : Ideal ℤ where
  carrier := ev0RR '' M
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, M.add_mem hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, M.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro n _ ⟨x, hx, rfl⟩
    refine ⟨(n : RRsub) * x, M.mul_mem_left _ hx, ?_⟩
    rw [map_mul, ev0RR_intCast]
    rfl

theorem mem_constTermImage {M : Ideal RRsub} {n : ℤ} :
    n ∈ constTermImage M ↔ ∃ g ∈ M, ev0RR g = n := Iff.rfl

/-- The ideal `(z) = ker ev₀` is proper. -/
theorem span_zElt_ne_top : Ideal.span {zElt} ≠ (⊤ : Ideal RRsub) := by
  rw [← ker_ev0RR, Ne, Ideal.eq_top_iff_one]
  simp [RingHom.mem_ker]

/-- **`prop:interesting` (i), core form.** A maximal ideal `M` of `ℛ_ℝ` with
`z ∉ M` contains an element of constant term `1`. -/
theorem typeIII_contains_one (M : Ideal RRsub) (hM : M.IsMaximal) (hz : zElt ∉ M) :
    ∃ g ∈ M, ev0RR g = 1 := by
  by_contra hcon
  push_neg at hcon
  -- `I = ev₀(M)` is a proper ideal of `ℤ`.
  have hItop : constTermImage M ≠ ⊤ := by
    intro h
    obtain ⟨g, hg, hg1⟩ := mem_constTermImage.mp (Ideal.eq_top_iff_one _ |>.mp h)
    exact hcon g hg hg1
  obtain ⟨Q, hQ, hIQ⟩ := Ideal.exists_le_maximal _ hItop
  haveI : Q.IsPrime := hQ.isPrime
  rcases int_prime_ideal Q with hQbot | ⟨p, hp, hQp⟩
  · -- `Q = (0)`: every element of `M` has constant term `0`, so `M ≤ (z)`.
    have hMz : M ≤ Ideal.span {zElt} := by
      rw [← ker_ev0RR]
      intro x hx
      have : ev0RR x ∈ Q := hIQ ⟨x, hx, rfl⟩
      rw [hQbot] at this
      exact RingHom.mem_ker.mpr (Ideal.mem_bot.mp this)
    exact hz ((hM.eq_of_le span_zElt_ne_top hMz) ▸ Ideal.subset_span rfl)
  · -- `Q = (p)`: then `M ≤ (z, p)`.
    haveI : Fact p.Prime := ⟨hp⟩
    have hMzp : M ≤ Ideal.span {zElt, (p : RRsub)} := by
      rw [← comap_ev0RR_span_int p]
      intro x hx
      exact hQp ▸ hIQ ⟨x, hx, rfl⟩
    have := hM.eq_of_le (span_zp_isMaximal p).ne_top hMzp
    exact hz (this ▸ Ideal.subset_span (Set.mem_insert _ _))

/-- **`prop:interesting` (i).** Let `M` be a maximal ideal of `ℛ_ℝ` of type (iii),
i.e. with `z ∉ M` and `M ∩ ℤ = 0`. Then there is `g ∈ M` with `ev₀ g = 1`;
in particular `M ∈ 𝔓₁`.

The hypothesis `hint` (`M ∩ ℤ = 0`) is part of the paper's definition of type
(iii) and is stated here for faithfulness, but it is not needed: it follows from
`hM` and `hz` by `trichotomy`. See `typeIII_contains_one`. -/
theorem typeIII_contains_one_add (M : Ideal RRsub) (hM : M.IsMaximal) (hz : zElt ∉ M)
    (hint : ∀ n : ℤ, (n : RRsub) ∈ M → n = 0) :
    ∃ g ∈ M, ev0RR g = 1 := by
  have _ := hint
  exact typeIII_contains_one M hM hz

/-- A type-(iii) maximal ideal lies in `𝔓₁`. -/
theorem typeIII_isInP1 (M : Ideal RRsub) (hM : M.IsMaximal) (hz : zElt ∉ M) :
    IsInP1 M := by
  obtain ⟨g, hg, hg1⟩ := typeIII_contains_one M hM hz
  exact ⟨g, hg, hg1 ▸ isUnit_one⟩

end RequestProject
