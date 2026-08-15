import RequestProject.Gates
import RequestProject.AffineControl

/-!
# Freezing of coefficients in the limit (Section "Proofs", Step 4)

This file formalizes the **coefficient freezing** step of the Section 3 construction
in the paper *Integer Coefficients Power Series with Prescribed Zero Sets* by
Bannon–Feldman.  Having established (in `Gates.lean`) that the partial products

`P_N(z) = ∏_{n<N} E_n(z / α n ; γ n)`

converge locally uniformly on the open unit disk `𝔻 = ball 0 1` to a holomorphic
limit `f(z) = ∏' n, E_n(z / α n ; γ n)`, we now show that each Taylor coefficient of
the limit is *frozen* at its finite stage: once a coefficient has been fixed at some
finite partial product it never changes again, so the Taylor coefficient of the
limit equals the Taylor coefficient of any sufficiently advanced partial product.

The argument has two independent ingredients:

* An analytic principle (`taylorCoeff_tendsto_of_tendstoLocallyUniformlyOn`): Taylor
  coefficients are continuous under local uniform convergence of holomorphic
  functions.  This is obtained by iterating `TendstoLocallyUniformlyOn.deriv` to
  transfer local uniform convergence to all iterated derivatives, and evaluating at
  `0`.

* An algebraic stabilization (`partialProd_taylorCoeff_step`): by the affine
  coefficient control lemma (`affine_coeff_low`), multiplying by the factor `E_N`
  leaves every coefficient of degree `≤ N` unchanged, so `[z^m] P_{N+1} = [z^m] P_N`
  whenever `m ≤ N`.

Combining the two, `[z^m] f = [z^m] P_N` for every `N ≥ m` (`gates_coeff_freeze`).
-/

open scoped BigOperators Topology

namespace RequestProject

open Complex Filter

/-- Iterated derivatives of a function holomorphic on an open set are holomorphic
there. -/
lemma iteratedDeriv_differentiableOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv k f) U := by
  have hA : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have : AnalyticOnNhd ℂ (iteratedDeriv k f) U := by
    induction k with
    | zero => simpa using hA
    | succ p ihp => rw [iteratedDeriv_succ]; exact ihp.deriv
  exact this.differentiableOn

/-- **Local uniform convergence transfers to all iterated derivatives.**  If a
sequence of functions holomorphic on an open set `U` converges locally uniformly to
`f` there, then for each `k` the `k`-th iterated derivatives converge locally
uniformly to the `k`-th iterated derivative of `f`. -/
lemma iteratedDeriv_tendstoLocallyUniformlyOn {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f)
      atTop U := by
  induction k with
  | zero => simpa using hconv
  | succ n ih =>
    have hd : ∀ᶠ (m : ℕ) in atTop,
        DifferentiableOn ℂ (fun z => iteratedDeriv n (F m) z) U := by
      filter_upwards with m using iteratedDeriv_differentiableOn hU (hF m) n
    have h := ih.deriv hd hU
    simp only [iteratedDeriv_succ]
    convert h using 1

/-- **Taylor coefficients are continuous under local uniform convergence.**  If a
sequence of functions holomorphic on an open set `U ∋ 0` converges locally uniformly
to `f`, then for each `m` the `m`-th Taylor coefficients converge to the `m`-th
Taylor coefficient of `f`. -/
lemma taylorCoeff_tendsto_of_tendstoLocallyUniformlyOn {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) (m : ℕ) :
    Tendsto (fun n => taylorCoeff m (F n)) atTop (nhds (taylorCoeff m f)) := by
  unfold taylorCoeff
  apply Tendsto.div_const
  exact (iteratedDeriv_tendstoLocallyUniformlyOn hU hF hconv m).tendsto_at h0

/-- **One stabilization step.**  Multiplying by the factor `E_N` does not change any
Taylor coefficient of degree `≤ N`: for `m ≤ N`,
`[z^m] P_{N+1} = [z^m] P_N`. -/
lemma partialProd_taylorCoeff_step (α γ : ℕ → ℂ) (hα_ne : ∀ n, α n ≠ 0)
    {m N : ℕ} (hmN : m ≤ N) :
    taylorCoeff m (fun z => ∏ n ∈ Finset.range (N + 1), E n (γ n) (z / α n)) =
      taylorCoeff m (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n)) := by
  have hfun : (fun z => ∏ n ∈ Finset.range (N + 1), E n (γ n) (z / α n))
      = (fun z => (∏ n ∈ Finset.range N, E n (γ n) (z / α n)) * E N (γ N) (z / α N)) := by
    funext z; rw [Finset.prod_range_succ]
  rw [hfun]
  have hdiff : Differentiable ℂ (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n)) := by
    have hprodeq : (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n))
         = ∏ n ∈ Finset.range N, (fun z => E n (γ n) (z / α n)) := by
      funext z; simp [Finset.prod_apply]
    rw [hprodeq]
    apply Differentiable.finset_prod
    intro n _
    exact (E_differentiable n (γ n)).comp (differentiable_id.div_const _)
  exact affine_coeff_low N (γ N) (α N) (hα_ne N) _ (hdiff.analyticAt 0) hmN

/-- **Coefficients stabilize from stage `m` on.**  For every `N ≥ m`,
`[z^m] P_N = [z^m] P_m`. -/
lemma partialProd_taylorCoeff_stable (α γ : ℕ → ℂ) (hα_ne : ∀ n, α n ≠ 0)
    {m N : ℕ} (hmN : m ≤ N) :
    taylorCoeff m (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n)) =
      taylorCoeff m (fun z => ∏ n ∈ Finset.range m, E n (γ n) (z / α n)) := by
  induction N, hmN using Nat.le_induction with
  | base => rfl
  | succ N hmN ih =>
    rw [partialProd_taylorCoeff_step α γ hα_ne hmN, ih]

/-- **Freezing of coefficients in the limit.**  Under the hypotheses of
`gates_convergence` (the rounding bound and `|α n| → 1`), for every `m` and every
`N ≥ m` the `m`-th Taylor coefficient of the holomorphic limit `∏' n, E_n(z/α n;γ n)`
equals the `m`-th Taylor coefficient of the partial product `∏_{n<N} E_n(z/α n;γ n)`.
In particular the coefficients of the limit are exactly the (frozen) coefficients of
the finite stages of the construction. -/
theorem gates_coeff_freeze (α γ : ℕ → ℂ) (hα_ne : ∀ n, α n ≠ 0)
    (hα_lim : Tendsto (fun n => ‖α n‖) atTop (𝓝 1))
    (hγ : ∀ n, ‖γ n - 1‖ ≤ Real.sqrt 2 / 2 * ((n : ℝ) + 1) * ‖α n‖ ^ (n + 1))
    {m N : ℕ} (hmN : m ≤ N) :
    taylorCoeff m (fun z => ∏' n, E n (γ n) (z / α n)) =
      taylorCoeff m (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n)) := by
  obtain ⟨hconv, _⟩ := gates_convergence α γ hα_ne hα_lim hγ
  have hF : ∀ k, DifferentiableOn ℂ
      (fun z => ∏ n ∈ Finset.range k, E n (γ n) (z / α n)) (Metric.ball (0 : ℂ) 1) := by
    intro k
    have hdiff : Differentiable ℂ (fun z => ∏ n ∈ Finset.range k, E n (γ n) (z / α n)) := by
      have hprodeq : (fun z => ∏ n ∈ Finset.range k, E n (γ n) (z / α n))
           = ∏ n ∈ Finset.range k, (fun z => E n (γ n) (z / α n)) := by
        funext z; simp [Finset.prod_apply]
      rw [hprodeq]
      apply Differentiable.finset_prod
      intro n _
      exact (E_differentiable n (γ n)).comp (differentiable_id.div_const _)
    exact hdiff.differentiableOn
  have htend := taylorCoeff_tendsto_of_tendstoLocallyUniformlyOn
    (U := Metric.ball (0 : ℂ) 1) Metric.isOpen_ball (by simp) hF hconv m
  have hevent : ∀ᶠ k in atTop,
      taylorCoeff m (fun z => ∏ n ∈ Finset.range k, E n (γ n) (z / α n))
        = taylorCoeff m (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n)) := by
    filter_upwards [eventually_ge_atTop N] with k hk
    rw [partialProd_taylorCoeff_stable α γ hα_ne (le_trans hmN hk),
        partialProd_taylorCoeff_stable α γ hα_ne hmN]
  have hconst : Tendsto
      (fun k => taylorCoeff m (fun z => ∏ n ∈ Finset.range k, E n (γ n) (z / α n))) atTop
      (nhds (taylorCoeff m (fun z => ∏ n ∈ Finset.range N, E n (γ n) (z / α n)))) :=
    Tendsto.congr' (Filter.EventuallyEq.symm hevent) tendsto_const_nhds
  exact tendsto_nhds_unique htend hconst

end RequestProject
