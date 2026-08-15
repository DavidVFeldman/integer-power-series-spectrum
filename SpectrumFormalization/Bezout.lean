import SpectrumFormalization.PrimesOutside

/-!
# The Bézout theorem: the true fragment, and a counterexample

The paper *Integer Coefficients Power Series with Prescribed Zero Sets* (v19)
states a conditional Bézout theorem (`thm:bezout`): if `f, g ∈ ℛ_ℝ` have disjoint
zero sets in `𝔻`, then `(f, g)` is contained in no type-(i) maximal ideal and no
real point-evaluation ideal, and (conditionally) `(f, g) = ℛ_ℝ`.

We formalize the part that is **true**:

* `pointIdeal_not_le_of_no_common_zero` — if `f, g` have no common zero in `𝔻`,
  then `(f, g)` is not contained in any point-evaluation ideal `P_a` (`a ∈ 𝔻`).

We also record that the **type-(i) part of the paper's theorem is false**:

* `bezout_typeI_counterexample` — there exist `f, g ∈ ℛ_ℝ` with no common zero in
  `𝔻` such that `(f, g)` *is* contained in a type-(i) maximal ideal (take
  `f = g = 2` and `M = (z, 2)`: the constant `2` never vanishes on `𝔻`, so `f, g`
  have empty — hence disjoint — zero sets, yet `(2) ⊆ (z, 2)`).

Consequently the paper's step "`z ∈ M` forces `f(0) = g(0) = 0`" and the ensuing
type-(i) non-containment do not hold as stated.

## The corrected theorem

The repair is to add the hypothesis that the **constant terms of `f` and `g` are
coprime integers** — exactly what type-(i) containment obstructs. With it we
prove:

* `bezout_not_le_typeI` — `(f, g)` is contained in no type-(i) maximal ideal;
* `bezout_not_le_pointIdeal` — `(f, g)` is contained in no point-evaluation
  ideal `P_a`, `a ∈ 𝔻`;
* `bezout_corrected` — conditionally on the hypothesis `(H)` that every type-(iii)
  maximal ideal is a point-evaluation ideal, `(f, g) = ℛ_ℝ`.

Finally `bezout_typeI_sharp` shows the coprimality hypothesis cannot be dropped:
for every rational prime `p`, `f = g = p` has empty zero set yet
`(p) ⊆ (z, p) ≠ ℛ_ℝ`.
-/

open Complex Weierstrass

namespace RequestProject

/-
**Bézout, true fragment.** If `f, g ∈ ℛ_ℝ` have no common zero at `a ∈ 𝔻`
(more precisely: `f(a) = 0 → g(a) ≠ 0`), then the ideal `(f, g)` is not contained
in the point-evaluation ideal `P_a`.
-/
theorem pointIdeal_not_le_of_no_common_zero (f g : RRsub) (a : ℂ) (ha : a ∈ 𝔻)
    (hdisj : (ODevalAt a ha) (RRsub.subtype f) = 0 → (ODevalAt a ha) (RRsub.subtype g) ≠ 0) :
    ¬ (Ideal.span {f, g} ≤ pointIdealRR a ha) := by
  intro h_contain;
  exact hdisj ( h_contain ( Ideal.subset_span ( Set.mem_insert _ _ ) ) ) ( h_contain ( Ideal.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) )

/-
**The type-(i) step of the paper's Bézout theorem is false.** There are
`f, g ∈ ℛ_ℝ` with disjoint (indeed empty) zero sets in `𝔻` whose ideal `(f, g)`
is contained in a type-(i) maximal ideal `M` (with `z ∈ M`).
-/
theorem bezout_typeI_counterexample :
    ∃ (f g : RRsub) (M : Ideal RRsub),
      (∀ a : ℂ, ∀ ha : a ∈ 𝔻,
        (ODevalAt a ha) (RRsub.subtype f) = 0 →
          (ODevalAt a ha) (RRsub.subtype g) ≠ 0) ∧
      M.IsMaximal ∧ zElt ∈ M ∧ Ideal.span {f, g} ≤ M := by
  -- Let's choose $f = g = (2 : RRsub)$.
  use (2 : RRsub), (2 : RRsub);
  refine' ⟨ Ideal.span { zElt, ( 2 : RRsub ) }, _, _, _, _ ⟩ <;> norm_num [ Ideal.span_le ];
  · intro a ha; erw [ ODevalAt_mk ] ;
    erw [ Subtype.coe_mk ] ; norm_num;
  · convert span_zp_isMaximal 2;
  · exact Ideal.subset_span ( Set.mem_insert _ _ );
  · exact Ideal.subset_span ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) )

/-! ## The corrected Bézout theorem -/

/-
Membership in a type-(i) maximal ideal `(z, p)` forces `p` to divide the
constant term.
-/
theorem dvd_ev0RR_of_mem_span_zp {p : ℕ} (x : RRsub)
    (hx : x ∈ Ideal.span {zElt, (p : RRsub)}) : (p : ℤ) ∣ ev0RR x := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hx
  refine ⟨ev0RR b, ?_⟩
  rw [← hab]
  simp [mul_comm]

/-- **Bézout, step (i).** If the constant terms of `f, g ∈ ℛ_ℝ` are coprime
integers, then `(f, g)` is contained in no type-(i) maximal ideal. -/
theorem bezout_not_le_typeI (f g : RRsub) (hcop : IsCoprime (ev0RR f) (ev0RR g))
    (M : Ideal RRsub) (hM : M.IsMaximal) (hz : zElt ∈ M) :
    ¬ (Ideal.span {f, g} ≤ M) := by
  intro hle
  obtain ⟨p, hp, rfl⟩ := (typeI_maximal_iff M hM).mp hz
  have hf : (p : ℤ) ∣ ev0RR f :=
    dvd_ev0RR_of_mem_span_zp f (hle (Ideal.subset_span (Set.mem_insert _ _)))
  have hg : (p : ℤ) ∣ ev0RR g :=
    dvd_ev0RR_of_mem_span_zp g
      (hle (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hunit : IsUnit (p : ℤ) := hcop.isUnit_of_dvd' hf hg
  rw [Int.isUnit_iff] at hunit
  rcases hunit with h | h
  · exact hp.one_lt.ne' (by exact_mod_cast h)
  · omega

/-- **Bézout, step (ii).** If `f, g ∈ ℛ_ℝ` have disjoint zero sets in `𝔻`, then
`(f, g)` is contained in no point-evaluation ideal. -/
theorem bezout_not_le_pointIdeal (f g : RRsub)
    (hdisj : ∀ (a : ℂ) (ha : a ∈ 𝔻), (ODevalAt a ha) (RRsub.subtype f) = 0 →
      (ODevalAt a ha) (RRsub.subtype g) ≠ 0)
    (a : ℂ) (ha : a ∈ 𝔻) : ¬ (Ideal.span {f, g} ≤ pointIdealRR a ha) :=
  pointIdeal_not_le_of_no_common_zero f g a ha (hdisj a ha)

/-- **Corrected Bézout theorem.** Let `f, g ∈ ℛ_ℝ` have disjoint zero sets in `𝔻`
(`hdisj`) and coprime constant terms (`hcop`). Assume `(H)`: every type-(iii)
maximal ideal of `ℛ_ℝ` (one not containing `z` and containing no nonzero
integer) is a point-evaluation ideal `P_a` for some `a ∈ 𝔻`. Then
`(f, g) = ℛ_ℝ`.

The coprimality hypothesis `hcop` repairs the paper's `thm:bezout`, whose
type-(i) step is false without it (`bezout_typeI_counterexample`,
`bezout_typeI_sharp`). -/
theorem bezout_corrected (f g : RRsub)
    (hdisj : ∀ (a : ℂ) (ha : a ∈ 𝔻), (ODevalAt a ha) (RRsub.subtype f) = 0 →
      (ODevalAt a ha) (RRsub.subtype g) ≠ 0)
    (hcop : IsCoprime (ev0RR f) (ev0RR g))
    (H : ∀ M : Ideal RRsub, M.IsMaximal → zElt ∉ M →
      (∀ n : ℤ, (n : RRsub) ∈ M → n = 0) →
      ∃ (a : ℂ) (ha : a ∈ 𝔻), M = pointIdealRR a ha) :
    Ideal.span {f, g} = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  rcases trichotomy M hM with hz | ⟨hz, hint⟩
  · exact bezout_not_le_typeI f g hcop M hM hz hle
  · obtain ⟨a, ha, rfl⟩ := H M hM hz hint
    exact bezout_not_le_pointIdeal f g hdisj a ha hle

/-- **Sharpness of the coprimality hypothesis.** For every rational prime `p`,
`f = g = p` have empty (hence disjoint) zero sets in `𝔻`, yet `(f, g)` is
contained in the type-(i) maximal ideal `(z, p)` and so is a proper ideal. This
generalizes `bezout_typeI_counterexample` (the case `p = 2`) and shows that
`bezout_corrected` genuinely needs `IsCoprime (ev0RR f) (ev0RR g)`. -/
theorem bezout_typeI_sharp (p : ℕ) (hp : p.Prime) :
    (∀ (a : ℂ) (ha : a ∈ 𝔻), (ODevalAt a ha) (RRsub.subtype (p : RRsub)) = 0 →
        (ODevalAt a ha) (RRsub.subtype (p : RRsub)) ≠ 0) ∧
      (Ideal.span {zElt, (p : RRsub)}).IsMaximal ∧
      Ideal.span {(p : RRsub), (p : RRsub)} ≤ Ideal.span {zElt, (p : RRsub)} ∧
      Ideal.span {(p : RRsub), (p : RRsub)} ≠ ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : ∀ (a : ℂ) (ha : a ∈ 𝔻),
      (ODevalAt a ha) (RRsub.subtype (p : RRsub)) = (p : ℂ) := by
    intro a ha
    rw [map_natCast, map_natCast]
  have hle : Ideal.span {(p : RRsub), (p : RRsub)} ≤ Ideal.span {zElt, (p : RRsub)} := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl) <;>
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨fun a ha h => absurd h ?_, span_zp_isMaximal p, hle, ?_⟩
  · rw [hval a ha]
    exact_mod_cast hp.ne_zero
  · intro htop
    exact (span_zp_isMaximal p).ne_top (top_le_iff.mp (htop ▸ hle))

end RequestProject