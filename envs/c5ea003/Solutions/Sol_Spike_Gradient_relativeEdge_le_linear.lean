-- Prove2me | solution 1 for Spike.Gradient.relativeEdge_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:19.272081+00:00
-- url     : https://prove2.me/submissions/94f43dad-7171-4ea5-93bb-06fbe183cd74

-- Sol generated from Probability/SpikeTruncationGradient.lean
import Mathlib
import Definitions.Def_Probability_SpikeTruncationGradient

/-!
# A monotone size density manufactures an "edge" component at a truncation
boundary — and only there

Fifth component of the round-85 resolution.  After the tiny-`v` stratum is
removed by the truncation `v ≥ 2^95`, a residual left-edge weight survives in
the *pooled* kept fit.  Stratifying by bit length localises it entirely in the
band `[96, 98)` adjacent to the truncation boundary, with nothing at `≥ 98`.
This file proves that such a pattern is exactly what a *monotone size density*
produces, with no positional mechanism at all.

Model.  A band of `2m` consecutive size cells carries weights `f 0, …, f (2m-1)`.
The "edge excess" is the lower half's mass minus the upper half's.

Main results.

* `Spike.Gradient.edgeExcess_nonneg` — for any antitone (nonincreasing) size
  density the edge excess is nonnegative: a spurious left-edge weight is
  automatic.
* `Spike.Gradient.edgeExcess_eq_zero_of_flat` — a flat density gives exactly
  zero edge excess: the effect is a gradient effect, not an edge effect.
* `Spike.Gradient.geometric_relativeEdge` — for the geometric density
  `f i = r ^ i` the *relative* edge excess is exactly `(1 − r^m)/(1 + r^m)`.
* `Spike.Gradient.relativeEdge_strictAnti` — that quantity is strictly
  decreasing in `r`: the flatter the local density, the weaker the apparent
  edge component.
* `Spike.Gradient.relativeEdge_le_linear` — the quantitative decay
  `(1 − r^m)/(1 + r^m) ≤ m (1 − r)`, so at fixed band width the apparent edge
  weight is `O(1 − r)`: it vanishes as the density flattens away from the
  truncation boundary.

Together with `Catalog/Probability/SpikeStratifiedEvidence.lean` (pooled
evidence ≤ stratified evidence + null gap) this identifies the surviving
"persistence" as a truncation-boundary size gradient.
-/

open Spike.Gradient








/-! ### The geometric (Dickman-like) local density -/








open Spike.Gradient in
theorem solution{r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1) (m : ℕ) :
    relativeEdge r m ≤ m * (1 - r) := by
  have hkey : 1 - r ^ m ≤ m * (1 - r) := by
    induction m with
    | zero => simp
    | succ k ih =>
        have hk : r ^ k ≤ 1 := pow_le_one₀ hr0 hr
        have : 1 - r ^ (k + 1) = (1 - r ^ k) + r ^ k * (1 - r) := by ring
        rw [this]
        have h2 : r ^ k * (1 - r) ≤ 1 * (1 - r) := by
          apply mul_le_mul_of_nonneg_right hk (by linarith)
        push_cast
        nlinarith
  have hrm : 0 ≤ r ^ m := pow_nonneg hr0 m
  have hden : (1:ℝ) ≤ 1 + r ^ m := by linarith
  have hnum : 0 ≤ 1 - r ^ m := by
    have : r ^ m ≤ 1 := pow_le_one₀ hr0 hr
    linarith
  calc relativeEdge r m = (1 - r ^ m) / (1 + r ^ m) := rfl
    _ ≤ (1 - r ^ m) / 1 := by
        apply div_le_div_of_nonneg_left hnum (by norm_num) hden
    _ = 1 - r ^ m := by ring
    _ ≤ m * (1 - r) := hkey
