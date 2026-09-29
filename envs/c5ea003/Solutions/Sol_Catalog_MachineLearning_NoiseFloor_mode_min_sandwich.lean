-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.mode_min_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:41:12.487343+00:00
-- url     : https://prove2.me/submissions/aae3b283-20c6-4332-aa06-7c78e581b098

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
theorem solution(hx : 0 ≤ x) (hb : 0 < b) :
    min x b / 2 ≤ x * b / (x + b) ∧ x * b / (x + b) ≤ min x b := by
  have hd : 0 < x + b := by linarith
  constructor
  · rcases le_total x b with h | h
    · rw [min_eq_left h, div_le_div_iff₀ (by norm_num) hd]
      nlinarith
    · rw [min_eq_right h, div_le_div_iff₀ (by norm_num) hd]
      nlinarith
  · refine le_min ?_ ?_
    · rw [div_le_iff₀ hd]; nlinarith
    · rw [div_le_iff₀ hd]; nlinarith
