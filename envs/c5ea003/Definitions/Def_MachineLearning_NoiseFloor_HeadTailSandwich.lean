-- Prove2me | Definitions.Def_MachineLearning_NoiseFloor_HeadTailSandwich
-- name    : MachineLearning_NoiseFloor_HeadTailSandwich
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:41.749645+00:00
-- url     : https://prove2.me/theorems/8d5f6a6a-c66e-4b68-bc6e-8e6f4bbf6b7c
-- title:
--   Aether Catalog definitions — MachineLearning_NoiseFloor_HeadTailSandwich
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NoiseFloor.HeadTailSandwich`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NoiseFloor/HeadTailSandwich.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
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

namespace Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]

/-- `∑ i, min (a i) b`: one noise unit per resolvable mode plus the energy of the
drowned modes. -/
noncomputable def minSum (a : ι → ℝ) (b : ℝ) : ℝ := ∑ i, min (a i) b

section Mode

variable {x b : ℝ}


end Mode

section Sandwich

variable {a : ι → ℝ} {b : ℝ}






end Sandwich

section Sharpness



end Sharpness

end Catalog.MachineLearning.NoiseFloor


