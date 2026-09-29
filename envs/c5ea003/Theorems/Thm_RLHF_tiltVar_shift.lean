-- Prove2me | Theorems.Thm_RLHF_tiltVar_shift
-- name    : RLHF.tiltVar_shift
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:49:15.786382+00:00
-- url     : https://prove2.me/theorems/5e9294f8-0395-43a3-ae1f-b92bb8142f96
-- title:
--   The variance of the reward under the tilted policy, computed around an arbitrary centre
-- statement:
--   The variance of the reward under the tilted policy, computed around an arbitrary centre
--   `a`: `Var = 𝔼(r − a)² − (𝔼r − a)²`.
--
--   ```lean
--   theorem RLHF.tiltVar_shift{r p : Ω → ℝ} (hp : ∀ y, 0 < p y) (a t : ℝ) :
--       tiltVar r p t
--         = (∑ y, tiltWeight r p t y * (r y - a) ^ 2) - (tiltMean r p t - a) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFVarianceSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFVarianceSharpness.lean#L52

-- Thm stub generated from NumberTheory/RLHFVarianceSharpness.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFVarianceCurvature
import Definitions.Def_NumberTheory_RLHFVarianceSharpness
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy

/-!
# Sharpness of the alignment speed limit, and curvature of the Euler factors

This file closes two of the three next-cycle sub-conjectures recorded in
`FUTURE_DIRECTIONS.md` after the curvature identity
`RLHF.deriv2_logExpMoment_eq_tiltVar` was proved.

**Sub-conjecture 1 (sharpness of the speed limit).**  `RLHF.tiltVar_le_range_sq` caps the
reward variance of a model confined to `[m, M]` by `(M − m)²/4`, and
`RLHF.tiltMean_drift_le` turns that into a temperature-uniform speed limit for alignment.
Here we show that the constant `1/4` cannot be improved and describe exactly when it is
attained:

* `RLHF.tiltVar_shift` — the variance of the tilted policy computed around an arbitrary
  centre.
* `RLHF.tiltVar_eq_range_sq_iff` — **the equality analysis**: the Popoviciu ceiling is
  attained at a temperature `t` if and only if the reward model is two-valued, taking only
  the extreme values `m` and `M`, *and* the tilted policy splits its mass evenly between the
  two levels (equivalently `𝔼_{π_t}[r] = (m+M)/2`).
* `RLHF.twoAtom_tiltVar`, `RLHF.twoAtom_tiltVar_zero` — the extremal model: the two-atom
  reward `r ∈ {0,1}` with balanced reference has `Var_{π_t}(r) = e^t/(1+e^t)²`, equal to
  `1/4` at `t = 0`.
* `RLHF.popoviciu_constant_sharp` and `RLHF.tiltMean_drift_constant_sharp` — consequently no
  constant below `1/4` can appear either in the variance ceiling or in the drift bound; the
  second statement is a genuine derivative argument (the slope of the logistic alignment
  curve at the origin).

**Sub-conjecture 2 (curvature of the Euler factors).**  The local zeta factor
`localZeta s p A = ∑_{k ≤ A} p^{-ks}` is the RLHF partition function of the reward
`k ↦ −k log p` on the exponent space `{0, …, A}` with uniform reference:

* `RLHF.expMoment_zero_geomReward` — the identification.
* `RLHF.convexOn_logLocalZeta`, `RLHF.strictConvexOn_logLocalZeta` — each Euler factor is
  log-convex in the exponent, strictly so for `p ≥ 2` and `A ≥ 1`.
* `RLHF.localZeta_curvature_eq_variance` — `d²/ds² log localZeta = Var(k log p)` under the
  truncated geometric law on exponents.
* `RLHF.zetaSum_curvature_additive` — **additive curvature decomposition**: the curvature of
  the truncated Euler product is the sum of the per-prime curvatures.  Alignment "difficulty"
  is a sum of independent local contributions.
-/

open RLHF

open Finset Filter Topology

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Variance around an arbitrary centre -/

theorem RLHF.tiltVar_shift{r p : Ω → ℝ} (hp : ∀ y, 0 < p y) (a t : ℝ) :
    tiltVar r p t
      = (∑ y, tiltWeight r p t y * (r y - a) ^ 2) - (tiltMean r p t - a) ^ 2 := by sorry
