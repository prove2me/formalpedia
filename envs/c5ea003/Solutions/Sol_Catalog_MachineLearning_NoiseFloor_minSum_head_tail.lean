-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.minSum_head_tail
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:44:00.665681+00:00
-- url     : https://prove2.me/submissions/1c4f2a8a-c6d0-47de-afa2-193e07170b57

-- Sol generated from MachineLearning/NoiseFloor/HeadTailSandwich.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_HeadTailSandwich
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part IV: the head/tail sandwich

Round-6 hypothesis closure, Phase A, cycle 2.

Parts I–III computed the noise floor exactly (`b · d_eff`, a resolvent trace).
This file explains *what that number is made of*.  Splitting the spectrum at the
noise level into a **head** `{i : b ≤ a i}` (resolvable modes) and a **tail**
`{i : a i < b}` (modes drowned in noise), we prove the two-sided estimate

  `(1/2) * (b * #head + ∑_{tail} a i)  ≤  noiseFloor a b  ≤  b * #head + ∑_{tail} a i`,

i.e. *the irreducible risk is, up to a factor two, one unit of noise per
resolvable mode plus the entire energy of the drowned modes*.  Both constants
are attained, so the factor two cannot be removed by any sharper argument that
only sees `min (a i) b`.

Two consequences of independent interest:

* `no_learning_below_noise` — if every mode is below the noise level, **no**
  spectral filter beats the do-nothing estimator by more than a factor two;
* `saturation_above_noise`  — if every mode is above the noise level, the floor
  is at least `n b / 2`, so risk grows linearly in the ambient dimension.

## Main results

* `mode_min_sandwich`, `minSum_head_tail`
* `noiseFloor_le_minSum`, `half_minSum_le_noiseFloor`
* `no_learning_below_noise`, `saturation_above_noise`
* `sandwich_upper_sharp`, `sandwich_lower_sharp` — sharpness of both constants
-/

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]



variable {x b : ℝ}




variable {a : ι → ℝ} {b : ℝ}












open Catalog.MachineLearning.NoiseFloor in
theorem solution[DecidableEq ι] (a : ι → ℝ) (b : ℝ) :
    minSum a b = b * ((univ.filter fun i => b ≤ a i).card : ℝ)
      + ∑ i ∈ univ.filter fun i => a i < b, a i := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun i => b ≤ a i)
    (fun i => min (a i) b)
  have h1 : ∑ i ∈ univ.filter fun i => b ≤ a i, min (a i) b
      = b * ((univ.filter fun i => b ≤ a i).card : ℝ) := by
    rw [Finset.sum_congr rfl fun i hi => min_eq_right (mem_filter.1 hi).2]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h2 : ∑ i ∈ univ.filter fun i => ¬ b ≤ a i, min (a i) b
      = ∑ i ∈ univ.filter fun i => a i < b, a i := by
    have hfe : (univ.filter fun i => ¬ b ≤ a i) = univ.filter fun i => a i < b := by
      apply Finset.filter_congr
      intro i _
      simp [not_le]
    rw [hfe]
    exact Finset.sum_congr rfl fun i hi => min_eq_left (le_of_lt (mem_filter.1 hi).2)
  rw [minSum, ← hsplit, h1, h2]
