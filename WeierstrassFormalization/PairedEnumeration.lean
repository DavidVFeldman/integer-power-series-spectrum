/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.PairedRounding

/-!
# The paired enumeration of a conjugation-invariant divisor

Constructs, from a conjugation-invariant effective divisor `D` with no zero at the
origin, a flat enumeration `(pairN, pairA u r)` forming a `PairedEnum`: the zeros in
the open upper half plane are enumerated as `u` and paired with their conjugates,
and the real zeros are enumerated as `r` and paired among themselves. Even slots
`2t` carry the conjugate pair `(u t, conj (u t))`, odd slots `2t+1` carry the real
pair `(r (2t), r (2t+1))`; the order function is `pairN k = k / 2`.

This supplies `exists_pairedEnum` (used in `IntegerRealization.lean`).
-/

open Complex Filter Topology

namespace Weierstrass

/-- Restrict a divisor to the points satisfying a predicate `P`. -/
def EffectiveDivisor.restrict (D : EffectiveDivisor) (P : ℂ → Prop) [DecidablePred P] :
    EffectiveDivisor where
  mult z := if P z then D.mult z else 0
  mult_eq_zero_of_not_mem_𝔻 z hz := by
    by_cases h : P z <;> simp [h, D.mult_eq_zero_of_not_mem_𝔻 z hz]
  finite_inter_compact K hK hKc := by
    apply Set.Finite.subset (D.finite_inter_compact K hK hKc)
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    refine ⟨hz.1, ?_⟩
    by_cases h : P z
    · simpa [h] using hz.2
    · simp [h] at hz

@[simp] theorem EffectiveDivisor.restrict_mult (D : EffectiveDivisor) (P : ℂ → Prop)
    [DecidablePred P] (z : ℂ) :
    (D.restrict P).mult z = if P z then D.mult z else 0 := rfl

/-- Enumeration of the strictly-upper-half-plane part of `D`; all enumerated points
have non-negative imaginary part. -/
theorem exists_enum_upper (D : EffectiveDivisor) :
    ∃ u : ℕ → ℂ, (∀ k, u k ≠ 0) ∧ (∀ k, 0 < (u k).im ∨ u k = 2) ∧
      (∀ z, z ≠ 0 → (if 0 < z.im then D.mult z else 0) = {k | u k = z}.ncard) ∧
      (∀ s : ℝ, s < 1 → {k | ‖u k‖ < s}.Finite) := by
  classical
  obtain ⟨u, hu0, hmult, hesc, hval⟩ :=
    exists_enum_of_effectiveDivisor (D.restrict (fun z => 0 < z.im))
  refine ⟨u, hu0, ?_, fun z hz => by simpa using hmult z hz, hesc⟩
  intro k
  rcases hval k with h | h
  · left
    by_contra hik
    simp only [EffectiveDivisor.restrict_mult, if_neg hik] at h
    exact h rfl
  · exact Or.inr h

/-- Enumeration of the real part of `D`; all enumerated points are real. -/
theorem exists_enum_real (D : EffectiveDivisor) :
    ∃ r : ℕ → ℂ, (∀ k, r k ≠ 0) ∧ (∀ k, (r k).im = 0) ∧
      (∀ z, z ≠ 0 → (if z.im = 0 then D.mult z else 0) = {k | r k = z}.ncard) ∧
      (∀ s : ℝ, s < 1 → {k | ‖r k‖ < s}.Finite) := by
  classical
  obtain ⟨r, hr0, hmult, hesc, hval⟩ :=
    exists_enum_of_effectiveDivisor (D.restrict (fun z => z.im = 0))
  refine ⟨r, hr0, ?_, fun z hz => by simpa using hmult z hz, hesc⟩
  -- each value is a support point (hence real, since the restricted divisor lives on the real axis)
  -- or the pad `2` (also real).
  intro k
  rcases hval k with h | h
  · -- `(D.restrict (·.im = 0)).mult (r k) ≠ 0` forces `(r k).im = 0`
    by_contra hik
    simp only [EffectiveDivisor.restrict_mult, hik] at h
    exact h rfl
  · rw [h]; norm_num

/-! ## The flat paired enumeration -/

/-- The order function: two factors per slot, so slot `s` occupies indices `2s, 2s+1`. -/
def pairN (k : ℕ) : ℕ := k / 2

/-- The flat zeros: even slots `s = 2t` carry the conjugate pair `(u t, conj (u t))`,
odd slots `s = 2t+1` carry the real pair `(r (2t), r (2t+1))`. -/
noncomputable def pairA (u r : ℕ → ℂ) (k : ℕ) : ℂ :=
  if (k / 2) % 2 = 0 then
    (if k % 2 = 0 then u (k / 4) else (starRingEnd ℂ) (u (k / 4)))
  else
    (if k % 2 = 0 then r (k / 2 - 1) else r (k / 2))

variable {u r : ℕ → ℂ}

@[simp] theorem pairA_four_mul (t : ℕ) : pairA u r (4 * t) = u t := by
  unfold pairA
  rw [show (4*t/2)%2 = 0 from by omega, show (4*t)%2 = 0 from by omega,
      show 4*t/4 = t from by omega]; simp

@[simp] theorem pairA_four_mul_add_one (t : ℕ) :
    pairA u r (4 * t + 1) = (starRingEnd ℂ) (u t) := by
  unfold pairA
  rw [show ((4*t+1)/2)%2 = 0 from by omega, show (4*t+1)%2 = 1 from by omega,
      show (4*t+1)/4 = t from by omega]; simp

@[simp] theorem pairA_four_mul_add_two (t : ℕ) : pairA u r (4 * t + 2) = r (2 * t) := by
  unfold pairA
  rw [show ((4*t+2)/2)%2 = 1 from by omega, show (4*t+2)%2 = 0 from by omega,
      show (4*t+2)/2-1 = 2*t from by omega]; simp

@[simp] theorem pairA_four_mul_add_three (t : ℕ) :
    pairA u r (4 * t + 3) = r (2 * t + 1) := by
  unfold pairA
  rw [show ((4*t+3)/2)%2 = 1 from by omega, show (4*t+3)%2 = 1 from by omega,
      show (4*t+3)/2 = 2*t+1 from by omega]; simp

/-
The paired enumeration satisfies the `PairedEnum` structural conditions.
-/
theorem pairedEnum_pairA (hu0 : ∀ k, u k ≠ 0) (hr0 : ∀ k, r k ≠ 0)
    (hrre : ∀ k, (r k).im = 0) :
    PairedEnum pairN (pairA u r) := by
  constructor <;> norm_num;
  any_goals unfold pairN; omega;
  · intro k; unfold pairA; split_ifs <;> simp_all +decide ;
  · exact fun a b hab => Nat.div_le_div_right hab;
  · intro k hk; rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ pairN ] ;
    · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ pairA ];
      grind +qlia;
    · omega

/-
The escape property transfers from `u` and `r` to the paired enumeration.
-/
theorem hesc_pairA (huesc : ∀ s : ℝ, s < 1 → {k | ‖u k‖ < s}.Finite)
    (hresc : ∀ s : ℝ, s < 1 → {k | ‖r k‖ < s}.Finite) :
    ∀ s : ℝ, s < 1 → {k | ‖pairA u r k‖ < s}.Finite := by
  intro s hs
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ∈ {j | ‖u j‖ < s} ∪ {j | ‖r j‖ < s}, j ≤ N := by
    exact Set.Finite.bddAbove ( Set.Finite.union ( huesc s hs ) ( hresc s hs ) );
  refine Set.finite_iff_bddAbove.mpr ⟨ 4 * N + 3, fun k hk => ?_ ⟩;
  rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ pairA ];
  · grind;
  · grind +suggestions

/-
The zero counts of the paired enumeration recombine the upper-half-plane and
real counts into the full multiplicity of a conjugation-invariant divisor.
-/
theorem count_pairA (D : EffectiveDivisor) (hD : D.ConjInvariant)
    (hupos : ∀ k, 0 < (u k).im ∨ u k = 2) (hrre : ∀ k, (r k).im = 0)
    (hucount : ∀ z, z ≠ 0 → (if 0 < z.im then D.mult z else 0) = {k | u k = z}.ncard)
    (hrcount : ∀ z, z ≠ 0 → (if z.im = 0 then D.mult z else 0) = {k | r k = z}.ncard)
    (z : ℂ) (hz𝔻 : ‖z‖ < 1) (hz : z ≠ 0) :
    D.mult z = {k | pairA u r k = z}.ncard := by
  by_cases hzim : z.im = 0;
  · have hz_real : z ≠ 2 := by
      rintro rfl; norm_num at hz𝔻;
    have hz_real : {k | pairA u r k = z} = (fun j => if j % 2 = 0 then 4 * (j / 2) + 2 else 4 * (j / 2) + 3) '' {j | r j = z} := by
      ext k; simp [pairA];
      constructor;
      · intro hk
        by_cases hk_even : k % 2 = 0;
        · grind;
        · split_ifs at hk <;> simp_all +decide;
          · cases hupos ( k / 4 ) <;> simp_all +decide [ Complex.ext_iff ];
          · exact ⟨ k / 2, hk, by split_ifs <;> omega ⟩;
      · grind;
    rw [ hz_real, Set.ncard_image_of_injective ];
    · rw [ ← hrcount z hz, if_pos hzim ];
    · intro a b; norm_num; split_ifs <;> omega;
  · cases lt_or_gt_of_ne hzim <;> simp_all +decide [ Set.ncard ];
    · -- Since $z.im < 0$, we have $pairA u r k = z$ if and only if $k = 4t + 1$ for some $t$ such that $u t = \overline{z}$.
      have h_eq : {k | pairA u r k = z} = (fun t => 4 * t + 1) '' {t | u t = starRingEnd ℂ z} := by
        ext k; simp [pairA];
        rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_mod ];
        · cases hupos ( 2 * ( 2 * k ) / 4 ) <;> simp_all +decide [ Complex.ext_iff ]; all_goals grind;
        · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ];
          · ring_nf; aesop;
          · grind;
      rw [ h_eq, Set.encard_congr ];
      convert hucount ( starRingEnd ℂ z ) _ using 1;
      · simp +decide [ Complex.conj_im ];
        rw [ if_pos ‹_›, hD ];
      · simp_all +decide [ Complex.ext_iff ];
      · symm;
        refine' Equiv.ofBijective ( fun x => ⟨ _, Set.mem_image_of_mem _ x.2 ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩ <;> aesop;
    · rw [ show { k | pairA u r k = z } = Set.image ( fun t => 4 * t ) { t | u t = z } from ?_ ];
      · convert hucount z hz using 1;
        · rw [ if_pos ‹_› ];
        · rw [ Set.encard_congr ];
          exact ⟨ fun x => ⟨ x.val / 4, by aesop ⟩, fun x => ⟨ 4 * x.val, by aesop ⟩, fun x => by aesop, fun x => by aesop ⟩;
      · ext k; simp [pairA];
        constructor <;> intro hk;
        · split_ifs at hk <;> simp_all +decide [ Complex.ext_iff ];
          · exact ⟨ k / 4, hk, by omega ⟩;
          · cases hupos ( k / 4 ) <;> linarith;
        · grind +qlia

/-- **The paired enumeration.** (The origin is automatically excluded: the
enumeration counts only points `≠ 0`, and the caller supplies the origin factor
separately, so no hypothesis on `D.mult 0` is needed here.) -/
theorem exists_pairedEnum (D : EffectiveDivisor) (hD : D.ConjInvariant) :
    ∃ (n : ℕ → ℕ) (a : ℕ → ℂ), PairedEnum n a ∧
      (∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite) ∧
      (∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → D.mult z = {k | a k = z}.ncard) := by
  obtain ⟨u, hu0, hupos, hucount, huesc⟩ := exists_enum_upper D
  obtain ⟨r, hr0, hrre, hrcount, hresc⟩ := exists_enum_real D
  exact ⟨pairN, pairA u r, pairedEnum_pairA hu0 hr0 hrre, hesc_pairA huesc hresc,
    fun z hz𝔻 hz => count_pairA D hD hupos hrre hucount hrcount z hz𝔻 hz⟩

end Weierstrass