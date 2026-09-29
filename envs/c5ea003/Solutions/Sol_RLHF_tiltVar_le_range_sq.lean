-- Prove2me | solution 1 for RLHF.tiltVar_le_range_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:27:41.248376+00:00
-- url     : https://prove2.me/submissions/d8040a27-001f-4935-b26c-3cf00a6c39ef

-- Sol generated from NumberTheory/RLHFVarianceCurvature.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFLogConvexity
import Definitions.Def_NumberTheory_RLHFVarianceCurvature
import Theorems.Thm_RLHF_tiltWeight_moment
import Theorems.Thm_RLHF_tiltWeight_pos
import Theorems.Thm_RLHF_tiltWeight_sum

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
    (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) (t : ℝ) :
    tiltVar r p t ≤ (M - m) ^ 2 / 4 := by
  set a := (m + M) / 2 with ha
  set mu := tiltMean r p t with hmu
  have hkey : tiltVar r p t = (∑ y, tiltWeight r p t y * (r y - a) ^ 2) - (mu - a) ^ 2 := by
    have h1 : ∀ y, tiltWeight r p t y * (r y - a) ^ 2
        = tiltWeight r p t y * r y ^ 2 - 2 * a * (tiltWeight r p t y * r y ^ 1)
          + a ^ 2 * tiltWeight r p t y := by
      intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, tiltWeight_moment 2 r p t, tiltWeight_moment 1 r p t,
      tiltWeight_sum hp t]
    have hmm : mu = expMoment 1 r p t / expMoment 0 r p t := rfl
    unfold tiltVar
    rw [← hmu, hmm]
    ring
  have hbound : ∑ y, tiltWeight r p t y * (r y - a) ^ 2 ≤ (M - m) ^ 2 / 4 := by
    have hle : ∀ y ∈ (univ : Finset Ω),
        tiltWeight r p t y * (r y - a) ^ 2 ≤ tiltWeight r p t y * ((M - m) ^ 2 / 4) := by
      intro y _
      have hsq : (r y - a) ^ 2 ≤ (M - m) ^ 2 / 4 := by
        have h1 := hm y
        have h2 := hM y
        rw [ha]
        nlinarith [sq_nonneg (r y - a)]
      exact mul_le_mul_of_nonneg_left hsq (tiltWeight_pos hp t y).le
    have hsum := Finset.sum_le_sum hle
    rwa [← Finset.sum_mul, tiltWeight_sum hp t, one_mul] at hsum
  nlinarith [sq_nonneg (mu - a)]
