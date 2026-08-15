import SpectrumFormalization.TypeIII

/-!
# Ultraproduct primes of `ℛ_ℝ`

This file formalizes the unconditional core of the sequel's
`prop:ultraproductprime`, parts (i)–(ii), **without** invoking Łoś's theorem.

Fix a set `Z ⊆ 𝔻` with `0 ∉ Z`, and an ultrafilter `𝒰` on `Z`. (The paper's
nonemptiness hypothesis on `Z` is automatic: an `Ultrafilter Z` carries a
`NeBot` witness, so `∅ ∉ 𝒰` and `Z` is nonempty.)
Mathlib's `Filter.Germ` over an ultrafilter with values in a field is itself a
field (`Mathlib.Order.Filter.FilterProduct`, the mechanism behind the
hyperreals), so evaluation along `Z` gives a ring homomorphism

`Φ : ℛ_ℝ →+* Germ (𝒰 : Filter Z) ℂ`, `Φ h = ⟦a ↦ h(a)⟧`,

into a field, and `P_𝒰 := ker Φ` is prime.

We prove:

* `ultraHom` / `ultraPrime` — the homomorphism and the ideal;
* `ultraPrime_isPrime` — `P_𝒰` is prime;
* `mem_ultraPrime` — `h ∈ P_𝒰 ↔ {a ∈ Z | h(a) = 0} ∈ 𝒰`;
* `zElt_not_mem_ultraPrime` — `z ∉ P_𝒰` (its germ is `a ↦ a`, which vanishes on
  `∅ ∉ 𝒰` since `0 ∉ Z`);
* `intCast_mem_ultraPrime_iff` — `P_𝒰 ∩ ℤ = 0`.

Hence `P_𝒰` is a prime of class (c) in the trichotomy `spec_trichotomy`.

*Report (W5.3).* Parts (iii)–(iv) of `prop:ultraproductprime` and the partition
property `prop:prime1ultrafilter` are **not** formalized here. They require
realizing prescribed zero sets `W ⊆ Z` by elements of `ℛ_ℝ` of constant term `1`
— i.e. Paper I's `integer_realization` transported into the `RRsub` ring model —
and they silently require the realized sets to be conjugation-invariant, a
hypothesis the paper omits: `thm:main` only realizes conjugation-invariant
divisors, so the printed statement is safe only for `Z ⊆ ℝ ∩ 𝔻`.
-/

open Complex Weierstrass

namespace RequestProject

section Ultraproduct

variable (Z : Set ℂ) (hZ : Z ⊆ 𝔻)

/-- Evaluation of an element of `ℛ_ℝ` at the points of `Z`, as a ring
homomorphism into the product `Z → ℂ`. -/
noncomputable def evalOnSet : RRsub →+* (Z → ℂ) :=
  Pi.ringHom fun a : Z => (ODevalAt (a : ℂ) (hZ a.2)).comp RRsub.subtype

@[simp] theorem evalOnSet_apply (h : RRsub) (a : Z) :
    evalOnSet Z hZ h a = ODevalAt (a : ℂ) (hZ a.2) (RRsub.subtype h) := rfl

variable (U : Ultrafilter Z)

/-- **`Φ`**: evaluation along `Z`, valued in the ultraproduct
`Germ (𝒰 : Filter Z) ℂ`. -/
noncomputable def ultraHom : RRsub →+* Filter.Germ (U : Filter Z) ℂ :=
  (Filter.Germ.coeRingHom (U : Filter Z)).comp (evalOnSet Z hZ)

/-- **`P_𝒰`**: the ultraproduct prime, the kernel of `Φ`. -/
noncomputable def ultraPrime : Ideal RRsub := RingHom.ker (ultraHom Z hZ U)

/-- **Membership criterion.** `h ∈ P_𝒰` iff the zero set of `h` in `Z` belongs to
the ultrafilter. -/
theorem mem_ultraPrime {h : RRsub} :
    h ∈ ultraPrime Z hZ U ↔
      {a : Z | ODevalAt (a : ℂ) (hZ a.2) (RRsub.subtype h) = 0} ∈ (U : Filter Z) := by
  rw [ultraPrime, RingHom.mem_ker]
  show ((evalOnSet Z hZ h : Z → ℂ) : Filter.Germ (U : Filter Z) ℂ) = 0 ↔ _
  rw [show (0 : Filter.Germ (U : Filter Z) ℂ) = ((0 : Z → ℂ) : Filter.Germ _ ℂ) from rfl,
    Filter.Germ.coe_eq]
  rfl

/-- **`P_𝒰` is prime**, being the kernel of a ring homomorphism into the field
`Germ (𝒰 : Filter Z) ℂ`. -/
theorem ultraPrime_isPrime : (ultraPrime Z hZ U).IsPrime :=
  RingHom.ker_isPrime _

end Ultraproduct

/-! ## Evaluation of `z` and of integer constants -/

/-- The coordinate element `z ∈ ℛ_ℝ` evaluates at `a ∈ 𝔻` to `a`. -/
theorem ODevalAt_zElt (a : ℂ) (ha : a ∈ 𝔻) :
    ODevalAt a ha (RRsub.subtype zElt) = a := by
  have hC : ∀ n : ℕ, ‖(((if n = 1 then (1 : ℤ) else 0) : ℤ) : ℂ)‖ ≤ (1 : ℝ) := by
    intro n; split_ifs <;> norm_num
  show psFun (fun n : ℕ => (((if n = 1 then (1 : ℤ) else 0) : ℤ) : ℂ)) a = a
  refine (psFun_hasSum hC ha).unique ?_
  have hfun : (fun n : ℕ => (((if n = 1 then (1 : ℤ) else 0) : ℤ) : ℂ) * a ^ n)
      = fun n : ℕ => if n = 1 then a else 0 := by
    funext n; split_ifs with h <;> simp [h]
  rw [hfun]
  exact hasSum_ite_eq 1 a

theorem ODevalAt_intCast (n : ℤ) (a : ℂ) (ha : a ∈ 𝔻) :
    ODevalAt a ha (RRsub.subtype (n : RRsub)) = (n : ℂ) := by
  rw [map_intCast, map_intCast]

section UltraproductFacts

variable {Z : Set ℂ} (hZ : Z ⊆ 𝔻) (h0 : (0 : ℂ) ∉ Z) (U : Ultrafilter Z)

include h0 in
/-- **`z ∉ P_𝒰`.** The germ of `z` is the inclusion `a ↦ a`, whose zero set in
`Z` is empty because `0 ∉ Z`; and `∅` is never a member of an ultrafilter. -/
theorem zElt_not_mem_ultraPrime : zElt ∉ ultraPrime Z hZ U := by
  rw [mem_ultraPrime]
  intro hmem
  have hempty : {a : Z | ODevalAt (a : ℂ) (hZ a.2) (RRsub.subtype zElt) = 0} = ∅ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [ODevalAt_zElt]
    intro ha
    exact h0 (ha ▸ a.2)
  rw [hempty] at hmem
  simp at hmem

/-- **`P_𝒰 ∩ ℤ = 0`.** An integer constant lies in `P_𝒰` only if it is zero. -/
theorem intCast_mem_ultraPrime_iff (n : ℤ) :
    (n : RRsub) ∈ ultraPrime Z hZ U ↔ n = 0 := by
  constructor
  · intro hmem
    by_contra hn
    rw [mem_ultraPrime] at hmem
    have hempty : {a : Z | ODevalAt (a : ℂ) (hZ a.2) (RRsub.subtype (n : RRsub)) = 0} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [ODevalAt_intCast]
      exact_mod_cast hn
    rw [hempty] at hmem
    simp at hmem
  · rintro rfl
    simp

include h0 in
/-- **`P_𝒰` is a prime of class (c)** in the trichotomy `spec_trichotomy`: it is
prime, does not contain `z`, and meets `ℤ` only in `0`. -/
theorem ultraPrime_isTypeC :
    (ultraPrime Z hZ U).IsPrime ∧ zElt ∉ ultraPrime Z hZ U ∧
      ∀ n : ℤ, (n : RRsub) ∈ ultraPrime Z hZ U → n = 0 :=
  ⟨ultraPrime_isPrime Z hZ U, zElt_not_mem_ultraPrime hZ h0 U,
    fun n hn => (intCast_mem_ultraPrime_iff hZ U n).mp hn⟩

end UltraproductFacts

end RequestProject
