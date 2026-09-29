-- Prove2me | Definitions.Def_Probability_SpikeTruncationGradient
-- name    : Probability_SpikeTruncationGradient
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:37.727986+00:00
-- url     : https://prove2.me/theorems/2938a128-4da1-4c1a-ad18-8aecbe7161df
-- title:
--   Aether Catalog definitions — Probability_SpikeTruncationGradient
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SpikeTruncationGradient`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SpikeTruncationGradient.lean by skeleton subtraction
import Mathlib

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

namespace Spike.Gradient

/-- Mass of the lower half of a band of `2m` size cells. -/
def lowerSum (f : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, f i

/-- Mass of the upper half of a band of `2m` size cells. -/
def upperSum (f : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.Ico m (2 * m), f i

/-- The apparent left-edge excess of the band. -/
def edgeExcess (f : ℕ → ℝ) (m : ℕ) : ℝ := lowerSum f m - upperSum f m





/-! ### The geometric (Dickman-like) local density -/

/-- The relative edge excess of a geometric density. -/
noncomputable def relativeEdge (r : ℝ) (m : ℕ) : ℝ := (1 - r ^ m) / (1 + r ^ m)






end Spike.Gradient


