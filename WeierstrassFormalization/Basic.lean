/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import Mathlib

/-!
# Basic setup for the Weierstrass-type construction

Common notation and definitions shared across the formalization of Bannon–Feldman,
*Integer Coefficients Power Series with Prescribed Zero Sets*:

* the open unit disk `𝔻`, with the membership characterization `mem_𝔻_iff`;
* `HolomorphicOn`, meaning analytic on a neighborhood of the whole disk;
* a convenience wrapper `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`
  computing the analytic order of a simple zero.
-/

open Complex

namespace Weierstrass

/-- The open unit disk `𝔻 = { z : ℂ | ‖z‖ < 1 }` in the complex plane. -/
notation "𝔻" => Metric.ball (0 : ℂ) 1

/-- Membership in the open unit disk is characterized by the norm being `< 1`. -/
theorem mem_𝔻_iff {z : ℂ} : z ∈ 𝔻 ↔ ‖z‖ < 1 := by
  rw [Metric.mem_ball, dist_zero_right]

/-- A function is *holomorphic on the disk* if it is analytic on a neighborhood of
every point of `𝔻`. -/
def HolomorphicOn (f : ℂ → ℂ) : Prop := AnalyticOnNhd ℂ f 𝔻

end Weierstrass

/-- If `f` is analytic at `x`, vanishes at `x`, and has nonzero derivative there,
then it has a simple zero: its analytic order at `x` equals `1`. -/
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hval : f x = 0) (hf' : deriv f x ≠ 0) :
    analyticOrderAt f x = 1 := by
  have h := hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'
  simpa [hval, sub_zero] using h
