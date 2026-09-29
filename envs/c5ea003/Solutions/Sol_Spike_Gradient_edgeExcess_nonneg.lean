-- Prove2me | solution 1 for Spike.Gradient.edgeExcess_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:18.311292+00:00
-- url     : https://prove2.me/submissions/7ecc08e7-87b1-4889-a37f-c9c88f4bd97f

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




theorem upperSum_eq (f : ℕ → ℝ) (m : ℕ) :
    upperSum f m = ∑ i ∈ Finset.range m, f (m + i) := by
  simp only [upperSum]
  rw [Finset.sum_Ico_eq_sum_range, show 2 * m - m = m by omega]




/-! ### The geometric (Dickman-like) local density -/








open Spike.Gradient in
theorem solution{f : ℕ → ℝ} (hf : ∀ i j, i ≤ j → f j ≤ f i) (m : ℕ) :
    0 ≤ edgeExcess f m := by
  simp only [edgeExcess, lowerSum, upperSum_eq]
  have : ∑ i ∈ Finset.range m, f (m + i) ≤ ∑ i ∈ Finset.range m, f i :=
    Finset.sum_le_sum fun i _ => hf i (m + i) (by omega)
  linarith
