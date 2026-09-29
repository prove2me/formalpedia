-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.geometric_scaling_upper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:42:24.470549+00:00
-- url     : https://prove2.me/submissions/c4e45702-bf56-401d-9cd2-b2665e23b5f1

-- Sol generated from MachineLearning/NoiseFloor/SpectralScalingLaw.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_HeadTailSandwich
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_geom_tail_le
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_mode_min_sandwich
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_noiseFloor_eq_sum
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

/-- The noise floor of the geometric spectrum, as a sum over `range n`. -/
lemma noiseFloor_geom_eq (r b : ℝ) (n : ℕ) :
    noiseFloor (fun i : Fin n => r ^ (i : ℕ)) b
      = ∑ i ∈ Finset.range n, r ^ i * b / (r ^ i + b) := by
  rw [noiseFloor_eq_sum]
  exact Fin.sum_univ_eq_sum_range (fun i => r ^ i * b / (r ^ i + b)) n








open Catalog.MachineLearning.NoiseFloor in
theorem solution(hr0 : 0 < r) (hr1 : r < 1) (hb : 0 < b) (n m : ℕ) :
    noiseFloor (fun i : Fin n => r ^ (i : ℕ)) b ≤ b * (m + 1) + r ^ (m + 1) / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  rw [noiseFloor_geom_eq]
  have hterm : ∀ i ∈ Finset.range n,
      r ^ i * b / (r ^ i + b) ≤ min (r ^ i) b := fun i _ =>
    (mode_min_sandwich (pow_nonneg hr0.le i) hb).2
  refine (Finset.sum_le_sum hterm).trans ?_
  have htail0 : (0:ℝ) ≤ r ^ (m + 1) / (1 - r) := by positivity
  rcases le_or_gt n (m + 1) with hn | hn
  · have hle : ∑ i ∈ Finset.range n, min (r ^ i) b ≤ ∑ _i ∈ Finset.range n, b :=
      Finset.sum_le_sum fun i _ => min_le_right _ _
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hnb : (n : ℝ) * b ≤ b * (m + 1) := by
      have : (n : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hn
      nlinarith
    linarith
  · rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt hn)]
    have hhead : ∑ i ∈ Finset.range (m + 1), min (r ^ i) b ≤ b * (m + 1) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) => min_le_right (r ^ i) b)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
      push_cast at this ⊢
      linarith
    have htail : ∑ i ∈ Finset.Ico (m + 1) n, min (r ^ i) b ≤ r ^ (m + 1) / (1 - r) := by
      refine le_trans (Finset.sum_le_sum fun i _ => min_le_left (r ^ i) b) ?_
      exact geom_tail_le hr0 hr1 (m + 1) n
    linarith
