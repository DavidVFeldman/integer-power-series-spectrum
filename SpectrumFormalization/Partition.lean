import SpectrumFormalization.OrderPlumbing

/-!
# The partition property (Tier B, `prop:prime1ultrafilter`)

Let `P` be a prime ideal of `ℛ_ℝ` containing an element `f` of constant term `1`
(so `P ∈ 𝔓₁`), and let `D` be the order divisor of `f` on `𝔻`. If `D` splits as
a sum `D = D₁ + D₂` of two **conjugation-invariant** effective divisors, then one
of the two pieces is again realized by an element of `P` of constant term `1`.

This is the manuscript's `prop:prime1ultrafilter` in divisor form: the family
`𝓕_Z(P)` of "pieces realized inside `P`" is closed under taking one part of any
conjugation-invariant partition.

*Discrepancy with the manuscript, as already recorded for the bridge.*
Conjugation-invariance of the pieces is an essential hypothesis, not a
convenience: Paper I realizes conjugation-invariant divisors only.
-/

open Complex Weierstrass

namespace RequestProject

/-- **Tier B: the partition property.** If a prime `P` contains an element `f` of
constant term `1` whose order divisor is `D`, and `D = D₁ + D₂` with `D₁`, `D₂`
conjugation-invariant effective divisors, then `P` contains an element of
constant term `1` whose order divisor is `D₁` or `D₂`. -/
theorem partition_property (P : Ideal RRsub) [P.IsPrime]
    (f : RRsub) (hf : f ∈ P) (hf0 : ev0RR f = 1)
    (D D₁ D₂ : EffectiveDivisor)
    (hD : ∀ a (ha : a ∈ 𝔻), ODorder a ha (RRsub.subtype f) = D.mult a)
    (hsum : ∀ a, D.mult a = D₁.mult a + D₂.mult a)
    (h₁ : D₁.ConjInvariant) (h₂ : D₂.ConjInvariant) :
    ∃ g ∈ P, ev0RR g = 1 ∧
      ((∀ a (ha : a ∈ 𝔻), ODorder a ha (RRsub.subtype g) = D₁.mult a) ∨
       (∀ a (ha : a ∈ 𝔻), ODorder a ha (RRsub.subtype g) = D₂.mult a)) := by
  -- The divisor has multiplicity `0` at the origin, hence so do both pieces.
  have hD0 : D.mult 0 = 0 := by
    rw [← hD 0 zero_mem_𝔻, ODorder_zero_of_ev0RR_eq_one hf0]
  have hD₁0 : D₁.mult 0 = 0 := by
    have := hsum 0
    omega
  have hD₂0 : D₂.mult 0 = 0 := by
    have := hsum 0
    omega
  -- Realize the two pieces.
  obtain ⟨F₁, hF₁0, hF₁⟩ := exists_RRsub_realization_order D₁ h₁ hD₁0
  obtain ⟨F₂, hF₂0, hF₂⟩ := exists_RRsub_realization_order D₂ h₂ hD₂0
  have hF₁ne : ev0RR F₁ ≠ 0 := by rw [hF₁0]; exact one_ne_zero
  have hF₂ne : ev0RR F₂ ≠ 0 := by rw [hF₂0]; exact one_ne_zero
  -- The product realizes `D` and has constant term `1`.
  have hprod0 : ev0RR (F₁ * F₂) = 1 := by rw [map_mul, hF₁0, hF₂0, mul_one]
  have hsame : SameZeroDivisor (F₁ * F₂) f := by
    intro a ha
    rw [ODorder_mul hF₁ne hF₂ne a ha, hF₁ a ha, hF₂ a ha, hD a ha, hsum a]
  -- Hence the product is an associate of `f`, so it lies in `P`.
  obtain ⟨u, _, hu⟩ := unit_quotient (F₁ * F₂) f hprod0 hf0 hsame
  have hmem : F₁ * F₂ ∈ P := by rw [hu]; exact P.mul_mem_left u hf
  rcases (Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hmem) with h | h
  · exact ⟨F₁, h, hF₁0, Or.inl hF₁⟩
  · exact ⟨F₂, h, hF₂0, Or.inr hF₂⟩

end RequestProject
