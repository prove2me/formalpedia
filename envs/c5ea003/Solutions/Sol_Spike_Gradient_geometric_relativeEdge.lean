-- Prove2me | solution 1 for Spike.Gradient.geometric_relativeEdge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:18.777909+00:00
-- url     : https://prove2.me/submissions/5bf5f943-dc1e-42e5-85d4-e3ad3a259ae4

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


theorem geom_lowerSum (r : ℝ) (hr : r ≠ 1) (m : ℕ) :
    lowerSum (fun i => r ^ i) m = (1 - r ^ m) / (1 - r) := by
  simp only [lowerSum]
  rw [geom_sum_eq hr, div_eq_div_iff (sub_ne_zero.mpr hr) (sub_ne_zero.mpr (Ne.symm hr))]
  ring

theorem geom_upperSum (r : ℝ) (hr : r ≠ 1) (m : ℕ) :
    upperSum (fun i => r ^ i) m = r ^ m * ((1 - r ^ m) / (1 - r)) := by
  rw [upperSum_eq]
  have : ∑ i ∈ Finset.range m, r ^ (m + i) = r ^ m * ∑ i ∈ Finset.range m, r ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
  rw [this, ← lowerSum, geom_lowerSum r hr m]





open Spike.Gradient in
theorem solution(r : ℝ) (hr0 : 0 < r) (hr : r < 1) {m : ℕ} (hm : 0 < m) :
    edgeExcess (fun i => r ^ i) m
      / (lowerSum (fun i => r ^ i) m + upperSum (fun i => r ^ i) m)
      = relativeEdge r m := by
  have hrne : r ≠ 1 := ne_of_lt hr
  have hpos : 0 < 1 - r := by linarith
  have hrm : r ^ m < 1 := pow_lt_one₀ hr0.le hr (by omega)
  have hrmpos : 0 < r ^ m := pow_pos hr0 m
  have h1 : (0:ℝ) < 1 + r ^ m := by linarith
  simp only [edgeExcess, geom_lowerSum r hrne, geom_upperSum r hrne, relativeEdge]
  rw [div_eq_div_iff]
  · ring
  · have hrw : (1 - r ^ m) / (1 - r) + r ^ m * ((1 - r ^ m) / (1 - r))
        = (1 + r ^ m) * ((1 - r ^ m) / (1 - r)) := by ring
    rw [hrw]
    have : 0 < (1 - r ^ m) / (1 - r) := div_pos (by linarith) hpos
    exact ne_of_gt (mul_pos h1 this)
  · exact ne_of_gt h1
