-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.geometric_scaling_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:41:11.825088+00:00
-- url     : https://prove2.me/submissions/22c5ba30-1c05-44b5-8c32-0a345b65f585

-- Sol generated from MachineLearning/NoiseFloor/SpectralScalingLaw.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_HeadTailSandwich
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
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
theorem solution(hr0 : 0 < r) (hr1 : r < 1) (hb : 0 < b) {n m : ℕ}
    (hmn : m + 1 ≤ n) (hbm : b ≤ r ^ m) :
    b * (m + 1) / 2 ≤ noiseFloor (fun i : Fin n => r ^ (i : ℕ)) b := by
  rw [noiseFloor_geom_eq]
  have hsub : Finset.range (m + 1) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hnonneg : ∀ i ∈ Finset.range n, i ∉ Finset.range (m + 1) →
      0 ≤ r ^ i * b / (r ^ i + b) := by
    intro i _ _
    have hp : (0:ℝ) ≤ r ^ i := pow_nonneg hr0.le i
    have : 0 < r ^ i + b := by linarith
    positivity
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg)
  have hhead : ∀ i ∈ Finset.range (m + 1), b / 2 ≤ r ^ i * b / (r ^ i + b) := by
    intro i hi
    have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hri : r ^ m ≤ r ^ i := pow_le_pow_of_le_one hr0.le hr1.le him
    have hbi : b ≤ r ^ i := le_trans hbm hri
    have hp : (0:ℝ) < r ^ i + b := by linarith
    rw [div_le_div_iff₀ (by norm_num) hp]
    nlinarith
  have := Finset.sum_le_sum hhead
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  push_cast at this
  linarith
