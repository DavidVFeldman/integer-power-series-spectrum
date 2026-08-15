import SpectrumFormalization.Bridge
import SpectrumFormalization.UnitQuotient

/-!
# Order-of-vanishing plumbing (Tier A)

The bridge `exists_RRsub_realization` speaks the language of
`Weierstrass.IsZeroDivisorOf`, while the unit-quotient lemma speaks the language
of `ODorder`. Both reduce to `analyticOrderNatAt` of a representative; this file
connects them once and for all, and records the basic calculus of `ODorder` on
`ℛ_ℝ`:

* `exists_RRsub_realization_order` (A.1) — divisor-level bridge;
* `ODorder_mul` (A.2) — additivity of `ODorder` on products;
* `ODevalAt_eq_zero_iff_ODorder_pos` (A.3) — value–order link;
* `ODorder_zero_of_ev0RR_eq_one` (A.4) — order `0` at the origin for constant
  term `1`.

The hypothesis in A.2–A.4 is `ev0RR x ≠ 0`: a nonzero value at one point of the
connected disk rules out, by the identity theorem, the degenerate case of a
locally (hence globally) vanishing representative, for which `analyticOrderNatAt`
returns the junk value `0`.
-/

open Complex Weierstrass

namespace RequestProject

/-! ## Finiteness of the analytic order on the disk -/

/-- On the connected disk, a function analytic on `𝔻` that is nonzero somewhere
has finite analytic order at every point of `𝔻`. -/
theorem analyticOrderAt_ne_top_of_apply_ne_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f 𝔻)
    {w : ℂ} (hw : w ∈ 𝔻) (hfw : f w ≠ 0) {a : ℂ} (ha : a ∈ 𝔻) :
    analyticOrderAt f a ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ z in nhds a, f z = 0 := analyticOrderAt_eq_top.mp htop
  have hpre : IsPreconnected (𝔻 : Set ℂ) := (convex_ball (0 : ℂ) 1).isPreconnected
  have hzero : Set.EqOn f 0 𝔻 :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre ha hev
  exact hfw (hzero hw)

/-! ## Representatives of elements of `ℛ_ℝ` -/

/-- A representative of `x : ℛ_ℝ` in `diskAnalytic`, with integer coefficients. -/
theorem exists_rep_RRsub (x : RRsub) :
    ∃ f : diskAnalytic, IsIntegerCoeffs (f : ℂ → ℂ) ∧ RRsub.subtype x = ODmk f := by
  obtain ⟨f, hfi, hfx⟩ := mem_RRsub.mp x.2
  exact ⟨f, hfi, hfx.symm⟩

/-- The value at `0` of a representative is the constant term. -/
theorem rep_apply_zero {x : RRsub} {f : diskAnalytic} (hf : RRsub.subtype x = ODmk f) :
    (f : ℂ → ℂ) 0 = ((ev0RR x : ℤ) : ℂ) := by
  have h := intCoeff_spec x 0
  rw [hf, ODtaylorCoeff_mk, taylorCoeff_zero_eq] at h
  rw [← h, ev0RR_eq]

/-- If `ev₀ x ≠ 0`, any representative of `x` has finite analytic order at every
point of `𝔻`. -/
theorem analyticOrderAt_rep_ne_top {x : RRsub} (hx : ev0RR x ≠ 0) {f : diskAnalytic}
    (hf : RRsub.subtype x = ODmk f) {a : ℂ} (ha : a ∈ 𝔻) :
    analyticOrderAt (f : ℂ → ℂ) a ≠ ⊤ := by
  refine analyticOrderAt_ne_top_of_apply_ne_zero f.2 (Metric.mem_ball_self one_pos) ?_ ha
  rw [rep_apply_zero hf]
  exact_mod_cast hx

/-! ## A.1 — divisor-level bridge -/

/-- **A.1.** A conjugation-invariant effective divisor `D` on `𝔻` with
`D.mult 0 = 0` is the order divisor of an element `F ∈ ℛ_ℝ` with `ev₀ F = 1`. -/
theorem exists_RRsub_realization_order (D : EffectiveDivisor)
    (hD : D.ConjInvariant) (h0 : D.mult 0 = 0) :
    ∃ F : RRsub, ev0RR F = 1 ∧
      ∀ (a : ℂ) (ha : a ∈ 𝔻), ODorder a ha (RRsub.subtype F) = D.mult a := by
  obtain ⟨F, g, hFg, hF0, hdiv⟩ := exists_RRsub_realization D hD h0
  refine ⟨F, hF0, fun a ha => ?_⟩
  rw [hFg, ODorder_mk]
  exact (hdiv a ha).symm

/-! ## A.2 — additivity of `ODorder` -/

/-- **A.2.** `ODorder` is additive on products of elements of `ℛ_ℝ` with nonzero
constant term. -/
theorem ODorder_mul {x y : RRsub} (hx : ev0RR x ≠ 0) (hy : ev0RR y ≠ 0)
    (a : ℂ) (ha : a ∈ 𝔻) :
    ODorder a ha (RRsub.subtype (x * y)) =
      ODorder a ha (RRsub.subtype x) + ODorder a ha (RRsub.subtype y) := by
  obtain ⟨f, _, hfx⟩ := exists_rep_RRsub x
  obtain ⟨g, _, hgy⟩ := exists_rep_RRsub y
  have hxy : RRsub.subtype (x * y) = ODmk (f * g) := by
    rw [map_mul, hfx, hgy, map_mul]
  rw [hxy, hfx, hgy, ODorder_mk, ODorder_mk, ODorder_mk]
  have hfa : AnalyticAt ℂ (f : ℂ → ℂ) a := f.2 a ha
  have hga : AnalyticAt ℂ (g : ℂ → ℂ) a := g.2 a ha
  have hcoe : ((f * g : diskAnalytic) : ℂ → ℂ) = (f : ℂ → ℂ) * (g : ℂ → ℂ) := rfl
  rw [hcoe]
  exact analyticOrderNatAt_mul hfa hga (analyticOrderAt_rep_ne_top hx hfx ha)
    (analyticOrderAt_rep_ne_top hy hgy ha)

/-! ## A.3 — value–order link -/

/-- **A.3.** For `x ∈ ℛ_ℝ` with nonzero constant term, `x` vanishes at `a ∈ 𝔻`
iff its order of vanishing there is positive. -/
theorem ODevalAt_eq_zero_iff_ODorder_pos {x : RRsub} (hx : ev0RR x ≠ 0)
    (a : ℂ) (ha : a ∈ 𝔻) :
    ODevalAt a ha (RRsub.subtype x) = 0 ↔ 0 < ODorder a ha (RRsub.subtype x) := by
  obtain ⟨f, _, hfx⟩ := exists_rep_RRsub x
  have hfa : AnalyticAt ℂ (f : ℂ → ℂ) a := f.2 a ha
  have hne : analyticOrderAt (f : ℂ → ℂ) a ≠ ⊤ := analyticOrderAt_rep_ne_top hx hfx ha
  rw [hfx, ODorder_mk, ODevalAt_mk]
  constructor
  · intro hzero
    have : analyticOrderAt (f : ℂ → ℂ) a ≠ 0 := hfa.analyticOrderAt_ne_zero.mpr hzero
    simpa [analyticOrderNatAt, ENat.toNat_eq_zero, hne, pos_iff_ne_zero] using this
  · intro hpos
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hpos.ne'

/-! ## A.4 — order at the origin -/

/-- `0 ∈ 𝔻`. -/
theorem zero_mem_𝔻 : (0 : ℂ) ∈ 𝔻 := Metric.mem_ball_self one_pos

/-- **A.4.** An element with unit constant term does not vanish at the origin,
so its order there is `0`. -/
theorem ODorder_zero_of_ev0RR_ne_zero {x : RRsub} (hx : ev0RR x ≠ 0) :
    ODorder 0 zero_mem_𝔻 (RRsub.subtype x) = 0 := by
  by_contra hpos
  have hlt : 0 < ODorder 0 zero_mem_𝔻 (RRsub.subtype x) := Nat.pos_of_ne_zero hpos
  have hzero := (ODevalAt_eq_zero_iff_ODorder_pos hx 0 zero_mem_𝔻).mpr hlt
  obtain ⟨f, _, hfx⟩ := exists_rep_RRsub x
  rw [hfx, ODevalAt_mk] at hzero
  rw [rep_apply_zero hfx] at hzero
  exact hx (by exact_mod_cast hzero)

/-- **A.4.** An element of constant term `1` has order `0` at the origin. -/
theorem ODorder_zero_of_ev0RR_eq_one {x : RRsub} (hx : ev0RR x = 1) :
    ODorder 0 zero_mem_𝔻 (RRsub.subtype x) = 0 :=
  ODorder_zero_of_ev0RR_ne_zero (by rw [hx]; exact one_ne_zero)

end RequestProject
