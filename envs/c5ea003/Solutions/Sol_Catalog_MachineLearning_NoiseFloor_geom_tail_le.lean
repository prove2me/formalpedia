-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.geom_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:41:11.29489+00:00
-- url     : https://prove2.me/submissions/cc39b3d8-305e-49df-b2dc-284b3a69e408

-- Sol generated from MachineLearning/NoiseFloor/SpectralScalingLaw.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_HeadTailSandwich
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part VIII: a formal scaling law

Round-6 hypothesis closure, Phase A, cycle 5.

Neural scaling laws assert that the irreducible risk of a model decays like a
power (or a power times a log) of the amount of data.  Parts I–VII reduce the
irreducible risk to the single functional `noiseFloor a b`, so a scaling law is
now a *computation with a fixed spectrum*, not a modelling assumption.

We carry this out for the geometric (exponentially decaying) spectrum
`a i = r ^ i`, `0 < r < 1`, at noise level `b = σ²/N`.  The head/tail sandwich
of Part IV yields matching bounds

  `b (m+1) / 2  ≤  noiseFloor  ≤  b (m+1) + r^{m+1} / (1 - r)`

for every cut index `m`, and taking the natural cut `r^{m+1} ≤ b ≤ r^m` gives

  `b (m+1) / 2  ≤  noiseFloor  ≤  b (m+1) + b / (1 - r)`,

i.e. `noiseFloor ≍ b · m ≍ b · log(1/b) / log(1/r)`: **the log-corrected `1/N`
law**, derived rather than assumed.

## Main results

* `noiseFloor_geom_eq`        — the floor of a geometric spectrum as a range sum
* `geometric_scaling_upper`   — upper bound for every cut `m`
* `geometric_scaling_lower`   — matching lower bound when `b ≤ r^m`
* `geometric_scaling_law`     — the two-sided law at the natural cut
-/

open Catalog.MachineLearning.NoiseFloor

open Finset


variable {r b : ℝ}









open Catalog.MachineLearning.NoiseFloor in
theorem solution(hr0 : 0 < r) (hr1 : r < 1) (k n : ℕ) :
    ∑ i ∈ Finset.Ico k n, r ^ i ≤ r ^ k / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  rw [Finset.sum_Ico_eq_sum_range]
  have hfac : ∑ j ∈ Finset.range (n - k), r ^ (k + j)
      = r ^ k * ∑ j ∈ Finset.range (n - k), r ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
  rw [hfac]
  have hgeom : ∑ j ∈ Finset.range (n - k), r ^ j ≤ 1 / (1 - r) := by
    rw [geom_sum_eq (by linarith : r ≠ 1)]
    have hK : (r ^ (n - k) - 1) / (r - 1) = (1 - r ^ (n - k)) / (1 - r) := by
      rw [div_eq_div_iff (by linarith : r - 1 ≠ 0) (by linarith : (1:ℝ) - r ≠ 0)]
      ring
    rw [hK, div_le_div_iff₀ h1r h1r]
    nlinarith [pow_nonneg hr0.le (n - k)]
  have hrk : (0:ℝ) ≤ r ^ k := pow_nonneg hr0.le k
  calc r ^ k * ∑ j ∈ Finset.range (n - k), r ^ j ≤ r ^ k * (1 / (1 - r)) := by
        exact mul_le_mul_of_nonneg_left hgeom hrk
    _ = r ^ k / (1 - r) := by ring
