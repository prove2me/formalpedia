-- Prove2me | Theorems.Thm_RLHF_hasDerivAt_logExpMoment
-- name    : RLHF.hasDerivAt_logExpMoment
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:39:38.001543+00:00
-- url     : https://prove2.me/theorems/53de069a-fd91-4b24-930a-894f0e4c8130
-- title:
--   `(log Z)'(t) = 𝔼_{π_t}[r]`: the slope of the value curve is the aligned expected
-- statement:
--   `(log Z)'(t) = 𝔼_{π_t}[r]`: the slope of the value curve is the aligned expected
--   reward.
--
--   ```lean
--   theorem RLHF.hasDerivAt_logExpMoment{r p : Ω → ℝ} (hp : ∀ y, 0 < p y) (t : ℝ) :
--       HasDerivAt (fun t => Real.log (expMoment 0 r p t)) (tiltMean r p t) t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFVarianceCurvature.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFVarianceCurvature.lean#L176

-- Thm stub generated from NumberTheory/RLHFVarianceCurvature.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFLogConvexity
import Definitions.Def_NumberTheory_RLHFVarianceCurvature

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

theorem RLHF.hasDerivAt_logExpMoment{r p : Ω → ℝ} (hp : ∀ y, 0 < p y) (t : ℝ) :
    HasDerivAt (fun t => Real.log (expMoment 0 r p t)) (tiltMean r p t) t := by sorry
