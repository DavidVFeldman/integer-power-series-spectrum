import SpectrumFormalization.Partition

/-!
# Ultraproduct trace and injectivity (Tier C, `prop:ultraproductprime` (ii)–(iv))

Standing data: a set `Z ⊆ 𝔻` of **real** points avoiding the origin, discrete in
`𝔻`, and an ultrafilter `𝒰` on `Z`. The manuscript's `prop:ultraproductprime`
constructs the prime `P_𝒰 = ker Φ_𝒰` (already available as `ultraPrime`) and
asserts, besides primeness:

* (ii) `P_𝒰 ∈ 𝔓₁` — `ultraPrime_isInP1`;
* (iii) the trace `𝓕_Z(P_𝒰) = 𝒰`, in the two directions
  `mem_ultraPrime_iff_zeroSet` (forward) and `exists_generator_of_mem`
  (backward);
* (iv) injectivity of `𝒰 ↦ P_𝒰` — `ultraPrime_injective`.

The realizations come from Tier A: every subset `W ⊆ Z` is the support of the
indicator divisor `indicatorDivisor W`, which is conjugation-invariant precisely
because the points of `Z` are real, and which avoids the origin because `0 ∉ Z`.
-/

open Complex Weierstrass
open scoped Classical

namespace RequestProject

/-! ## C.1 — indicator divisors -/

/-- The **indicator divisor** of a set `W` of points of `𝔻`, discrete in `𝔻`:
multiplicity `1` on `W` and `0` elsewhere. -/
noncomputable def indicatorDivisor (W : Set ℂ) (hW𝔻 : W ⊆ 𝔻)
    (hWfin : ∀ K ⊆ 𝔻, IsCompact K → (W ∩ K).Finite) : EffectiveDivisor where
  mult a := if a ∈ W then 1 else 0
  mult_eq_zero_of_not_mem_𝔻 z hz := by
    have hzW : z ∉ W := fun h => hz (hW𝔻 h)
    rw [if_neg hzW]
  finite_inter_compact K hK hKc := by
    have hsub : {z ∈ K | (if z ∈ W then 1 else 0) ≠ 0} ⊆ W ∩ K := by
      rintro z ⟨hzK, hzne⟩
      by_cases hzW : z ∈ W
      · exact ⟨hzW, hzK⟩
      · rw [if_neg hzW] at hzne; exact absurd rfl hzne
    exact (hWfin K hK hKc).subset hsub

@[simp] theorem indicatorDivisor_mult (W : Set ℂ) (hW𝔻 : W ⊆ 𝔻)
    (hWfin : ∀ K ⊆ 𝔻, IsCompact K → (W ∩ K).Finite) (a : ℂ) :
    (indicatorDivisor W hW𝔻 hWfin).mult a = if a ∈ W then 1 else 0 := rfl

/-- An indicator divisor supported on **real** points is conjugation-invariant. -/
theorem indicatorDivisor_conjInvariant (W : Set ℂ) (hW𝔻 : W ⊆ 𝔻)
    (hWfin : ∀ K ⊆ 𝔻, IsCompact K → (W ∩ K).Finite)
    (hWℝ : ∀ z ∈ W, z.im = 0) :
    (indicatorDivisor W hW𝔻 hWfin).ConjInvariant := by
  intro z
  have key : ∀ w ∈ W, (starRingEnd ℂ) w = w := fun w hw =>
    Complex.conj_eq_iff_im.mpr (hWℝ w hw)
  have hiff : (starRingEnd ℂ) z ∈ W ↔ z ∈ W := by
    constructor
    · intro h
      have h2 : (starRingEnd ℂ) ((starRingEnd ℂ) z) = (starRingEnd ℂ) z := key _ h
      rw [Complex.conj_conj] at h2
      rwa [h2]
    · intro h; rwa [key z h]
  simp only [indicatorDivisor_mult]
  by_cases h : z ∈ W
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

/-- An indicator divisor of a set avoiding the origin has multiplicity `0` there. -/
theorem indicatorDivisor_mult_zero (W : Set ℂ) (hW𝔻 : W ⊆ 𝔻)
    (hWfin : ∀ K ⊆ 𝔻, IsCompact K → (W ∩ K).Finite) (h0 : (0 : ℂ) ∉ W) :
    (indicatorDivisor W hW𝔻 hWfin).mult 0 = 0 := by
  rw [indicatorDivisor_mult, if_neg h0]

section Trace

variable {Z : Set ℂ} (hZ𝔻 : Z ⊆ 𝔻) (hZℝ : ∀ z ∈ Z, z.im = 0) (h0 : (0 : ℂ) ∉ Z)
  (hfin : ∀ K ⊆ 𝔻, IsCompact K → (Z ∩ K).Finite)

include hZ𝔻 hZℝ h0 hfin in
/-- **C.2 (realizing subsets).** Every subset `W` of a real-supported, discrete
set `Z ⊆ 𝔻 \ {0}` is exactly the zero set in `𝔻` of an element of `ℛ_ℝ` of
constant term `1`. -/
theorem exists_realizer (W : Set ℂ) (hW : W ⊆ Z) :
    ∃ F : RRsub, ev0RR F = 1 ∧
      ∀ (a : ℂ) (ha : a ∈ 𝔻),
        (ODevalAt a ha (RRsub.subtype F) = 0 ↔ a ∈ W) := by
  have hW𝔻 : W ⊆ 𝔻 := hW.trans hZ𝔻
  have hWfin : ∀ K ⊆ 𝔻, IsCompact K → (W ∩ K).Finite := fun K hK hKc =>
    (hfin K hK hKc).subset (fun z hz => ⟨hW hz.1, hz.2⟩)
  have hWℝ : ∀ z ∈ W, z.im = 0 := fun z hz => hZℝ z (hW hz)
  have hW0 : (0 : ℂ) ∉ W := fun hz => h0 (hW hz)
  obtain ⟨F, hF0, hFord⟩ :=
    exists_RRsub_realization_order (indicatorDivisor W hW𝔻 hWfin)
      (indicatorDivisor_conjInvariant W hW𝔻 hWfin hWℝ)
      (indicatorDivisor_mult_zero W hW𝔻 hWfin hW0)
  refine ⟨F, hF0, fun a ha => ?_⟩
  have hne : ev0RR F ≠ 0 := by rw [hF0]; exact one_ne_zero
  rw [ODevalAt_eq_zero_iff_ODorder_pos hne a ha, hFord a ha, indicatorDivisor_mult]
  by_cases h : a ∈ W
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => Nat.zero_lt_one⟩
  · rw [if_neg h]; exact ⟨fun hc => absurd hc (lt_irrefl 0), fun hc => absurd hc h⟩

/-! ## C.3 — the trace, forward direction -/

/-- The zero set in `𝔻` of an element of `ℛ_ℝ`. -/
def zeroSetIn (h : RRsub) : Set ℂ :=
  {a | ∃ ha : a ∈ 𝔻, ODevalAt a ha (RRsub.subtype h) = 0}

theorem mem_zeroSetIn {h : RRsub} {a : ℂ} (ha : a ∈ 𝔻) :
    a ∈ zeroSetIn h ↔ ODevalAt a ha (RRsub.subtype h) = 0 :=
  ⟨fun ⟨_, h'⟩ => h', fun h' => ⟨ha, h'⟩⟩

omit hZℝ h0 hfin in
include hZ𝔻 in
/-- **C.3 (trace, forward).** `h ∈ P_𝒰` iff the trace on `Z` of the zero set of
`h` belongs to `𝒰`. (The hypothesis of the work order restricting the zero set
of `h` to lie inside `Z` is not needed for this equivalence.) -/
theorem mem_ultraPrime_iff_zeroSet (U : Ultrafilter Z) (h : RRsub) :
    h ∈ ultraPrime Z hZ𝔻 U ↔ (Subtype.val ⁻¹' zeroSetIn h : Set Z) ∈ (U : Filter Z) := by
  rw [mem_ultraPrime]
  have hset : {a : Z | ODevalAt (a : ℂ) (hZ𝔻 a.2) (RRsub.subtype h) = 0}
      = (Subtype.val ⁻¹' zeroSetIn h : Set Z) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact (mem_zeroSetIn (hZ𝔻 a.2)).symm
  rw [hset]

/-! ## C.4 — the trace, backward direction -/

include hZ𝔻 hZℝ h0 hfin in
/-- **C.4 (trace, backward).** Every member `S` of the ultrafilter is the trace on
`Z` of the zero set of an element of `P_𝒰` of constant term `1`. -/
theorem exists_generator_of_mem (U : Ultrafilter Z) (S : Set Z) (hS : S ∈ (U : Filter Z)) :
    ∃ F ∈ ultraPrime Z hZ𝔻 U, ev0RR F = 1 ∧
      ∀ a : Z, (ODevalAt (a : ℂ) (hZ𝔻 a.2) (RRsub.subtype F) = 0 ↔ a ∈ S) := by
  obtain ⟨F, hF0, hFzero⟩ :=
    exists_realizer hZ𝔻 hZℝ h0 hfin (Subtype.val '' S) (by
      rintro _ ⟨a, _, rfl⟩; exact a.2)
  have hmemS : ∀ a : Z, (ODevalAt (a : ℂ) (hZ𝔻 a.2) (RRsub.subtype F) = 0 ↔ a ∈ S) := by
    intro a
    rw [hFzero (a : ℂ) (hZ𝔻 a.2)]
    constructor
    · rintro ⟨b, hbS, hb⟩
      exact (Subtype.ext hb : b = a) ▸ hbS
    · intro h; exact ⟨a, h, rfl⟩
  refine ⟨F, ?_, hF0, hmemS⟩
  rw [mem_ultraPrime]
  have hset : {a : Z | ODevalAt (a : ℂ) (hZ𝔻 a.2) (RRsub.subtype F) = 0} = S := by
    ext a; exact hmemS a
  rw [hset]; exact hS

/-! ## C.5 — `P_𝒰 ∈ 𝔓₁` -/

include hZ𝔻 hZℝ h0 hfin in
/-- **C.5.** The ultraproduct prime lies in `𝔓₁`: it contains an element of
constant term `1` (the realizer of all of `Z`). -/
theorem ultraPrime_isInP1 (U : Ultrafilter Z) : IsInP1 (ultraPrime Z hZ𝔻 U) := by
  obtain ⟨F, hFmem, hF0, _⟩ :=
    exists_generator_of_mem hZ𝔻 hZℝ h0 hfin U Set.univ Filter.univ_mem
  exact ⟨F, hFmem, hF0 ▸ isUnit_one⟩

/-! ## C.6 — injectivity -/

include hZ𝔻 hZℝ h0 hfin in
/-- **C.6 (`prop:ultraproductprime` (iv)).** The map `𝒰 ↦ P_𝒰` is injective. -/
theorem ultraPrime_injective :
    Function.Injective (fun U : Ultrafilter Z => ultraPrime Z hZ𝔻 U) := by
  intro U₁ U₂ hEq
  have hEq' : ultraPrime Z hZ𝔻 U₁ = ultraPrime Z hZ𝔻 U₂ := hEq
  have hsub : ∀ S : Set Z, S ∈ (U₁ : Filter Z) → S ∈ (U₂ : Filter Z) := by
    intro S hS
    obtain ⟨F, hFmem, _, hFzero⟩ := exists_generator_of_mem hZ𝔻 hZℝ h0 hfin U₁ S hS
    have hF2 : F ∈ ultraPrime Z hZ𝔻 U₂ := hEq' ▸ hFmem
    rw [mem_ultraPrime] at hF2
    have hset : {a : Z | ODevalAt (a : ℂ) (hZ𝔻 a.2) (RRsub.subtype F) = 0} = S := by
      ext a; exact hFzero a
    rwa [hset] at hF2
  exact (Ultrafilter.eq_of_le (fun S hS => hsub S hS)).symm

end Trace

end RequestProject
