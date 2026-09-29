-- Prove2me | solution 1 for RLHF.tiltMean_drift_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:31:07.537873+00:00
-- url     : https://prove2.me/submissions/b456ac6e-e3de-4168-b3c6-fdf927b75ed2

-- Sol generated from NumberTheory/RLHFVarianceCurvature.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFLogConvexity
import Definitions.Def_NumberTheory_RLHFVarianceCurvature
import Theorems.Thm_RLHF_hasDerivAt_tiltMean
import Theorems.Thm_RLHF_tiltVar_le_range_sq

/-!
# Curvature of the RLHF value curve is the reward variance

The previous cycle proved *midpoint* log-convexity of the RLHF partition function
(`RLHF.expSum_sq_le`, `RLHF.expSum_sq_lt`) by Cauchy–Schwarz, and listed the differential
identity behind it as the first open sub-conjecture: the second derivative of `log Z` should
be the reward variance under the tilted (Gibbs) policy.  This file proves that identity and
harvests it.

Writing `t = 1/β` for the inverse KL temperature and

```
M_k(t) = ∑_y p y · (r y)^k · exp (r y · t)
```

for the exponential moments of the reward model, the main results are:

* `RLHF.hasDerivAt_expMoment` — `M_k' = M_{k+1}`: differentiating the partition function
  raises the moment index.  (Induction-free but genuinely analytic: a finite sum of
  `HasDerivAt`s.)
* `RLHF.hasDerivAt_logExpMoment` — `(log M_0)' = M_1 / M_0 = 𝔼_{π_t}[r]`, the aligned
  expected reward.
* `RLHF.hasDerivAt_tiltMean` and `RLHF.deriv2_logExpMoment_eq_tiltVar` — **the curvature
  identity** `(log M_0)'' = Var_{π_t}(r)`, with `RLHF.tiltVar_eq_sum` exhibiting the
  curvature as an honest sum of squares.
* `RLHF.convexOn_logExpMoment` and `RLHF.strictConvexOn_logExpMoment` — consequently
  `t ↦ log Z(t)` is convex on all of `ℝ`, and *strictly* convex as soon as the reward model
  is non-constant.  This upgrades the midpoint statements of `RLHFLogConvexity` to full
  convexity, and `RLHF.freeEnergy_convex_comb` transports it to the temperature variable:
  the normalized alignment value obeys the annealing inequality for *every* convex
  combination of inverse temperatures, not only the harmonic midpoint.
* `RLHF.tiltMean_monotone`, `RLHF.tiltVar_le_range_sq` and `RLHF.tiltMean_drift_le` — a
  **speed limit for alignment**: the aligned expected reward is monotone in the inverse
  temperature, its rate of increase is the variance, and Popoviciu's inequality caps that
  variance by `(M − m)²/4` for a reward model confined to `[m, M]`, uniformly in the size of
  the response space.
* `RLHF.integral_tiltVar` — the **variance-flow identity**
  `∫_{t₁}^{t₂} Var_{π_t}(r) dt = 𝔼_{π_{t₂}}[r] − 𝔼_{π_{t₁}}[r]`, the exact form of the speed
  limit above.
* `RLHF.convexOn_truncZetaLog` and `RLHF.strictConvexOn_truncZetaLog` — the arithmetic
  shadow: `s ↦ log (∑_{n=1}^{N} n^{-s})` is strictly convex on `ℝ` for `N ≥ 2`, i.e. the
  truncated Riemann zeta function is strictly log-convex in the exponent, and its curvature
  is the variance of `log n` under the truncated zeta distribution
  (`RLHF.truncZeta_curvature_eq_variance`).
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Exponential moments of the reward model -/






/-! ## 2. The tilted policy, its mean reward and its reward variance -/









/-! ## 3. First and second derivatives of the log-partition function -/






/-! ## 4. Full convexity of the value curve -/






/-! ## 5. Monotone alignment and the Popoviciu ceiling on alignment speed -/









/-! ## 6. Arithmetic shadow: strict log-convexity of the truncated zeta function -/













open RLHF in
theorem solution{r p : Ω → ℝ} (hp : ∀ y, 0 < p y) {m M : ℝ}
    (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) :
    tiltMean r p t₂ - tiltMean r p t₁ ≤ (t₂ - t₁) * ((M - m) ^ 2 / 4) := by
  set C := (M - m) ^ 2 / 4 with hC
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => C * t - tiltMean r p t)
      (C - tiltVar r p t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => C * t) C t := by
      simpa using (hasDerivAt_id t).const_mul C
    simpa using h1.sub (hasDerivAt_tiltMean hp t)
  have hmono : Monotone (fun t => C * t - tiltMean r p t) := by
    refine monotone_of_deriv_nonneg (fun t => (hderiv t).differentiableAt) (fun t => ?_)
    rw [(hderiv t).deriv]
    have := tiltVar_le_range_sq hp hm hM t
    linarith
  have := hmono ht
  simp only at this
  nlinarith [this]
