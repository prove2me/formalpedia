-- Prove2me | Theorems.Thm_Spike_Gradient_edgeExcess_nonneg
-- name    : Spike.Gradient.edgeExcess_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:06:46.656916+00:00
-- url     : https://prove2.me/theorems/d7e3fb10-e9e1-46ff-b8b3-6080fe5351ee
-- title:
--   **A nonincreasing size density always produces a nonnegative edge
-- statement:
--   **A nonincreasing size density always produces a nonnegative edge
--   excess.**  No positional mechanism is needed.
--
--   ```lean
--   theorem Spike.Gradient.edgeExcess_nonneg{f : ℕ → ℝ} (hf : ∀ i j, i ≤ j → f j ≤ f i) (m : ℕ) :
--       0 ≤ edgeExcess f m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SpikeTruncationGradient.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SpikeTruncationGradient.lean#L54

-- Thm stub generated from Probability/SpikeTruncationGradient.lean
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

theorem Spike.Gradient.edgeExcess_nonneg{f : ℕ → ℝ} (hf : ∀ i j, i ≤ j → f j ≤ f i) (m : ℕ) :
    0 ≤ edgeExcess f m := by sorry
