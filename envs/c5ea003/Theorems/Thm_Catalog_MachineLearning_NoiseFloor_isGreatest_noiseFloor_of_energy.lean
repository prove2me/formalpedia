-- Prove2me | Theorems.Thm_Catalog_MachineLearning_NoiseFloor_isGreatest_noiseFloor_of_energy
-- name    : Catalog.MachineLearning.NoiseFloor.isGreatest_noiseFloor_of_energy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:28:33.504227+00:00
-- url     : https://prove2.me/theorems/7c4923d6-227a-42d9-a41f-8d26aacc03e5
-- title:
--   The minimax noise floor.
-- statement:
--   **The minimax noise floor.**  `S b n / (S + n b)` is the greatest value the
--   noise floor can take on spectra of energy `S`, and it is attained (by the flat
--   spectrum).  Equivalently: the value of the game "adversary picks the signal of
--   energy `S`, learner picks the spectral filter" is `S b n / (S + n b)`.
--
--   ```lean
--   theorem Catalog.MachineLearning.NoiseFloor.isGreatest_noiseFloor_of_energy[Nonempty ι] (hb : 0 < b) (hS0 : 0 ≤ S) :
--       IsGreatest {r : ℝ | ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i = S) ∧ noiseFloor a b = r}
--         (S * b * (Fintype.card ι : ℝ) / (S + (Fintype.card ι : ℝ) * b)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NoiseFloor/MinimaxSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NoiseFloor/MinimaxSpectrum.lean#L111

-- Thm stub generated from MachineLearning/NoiseFloor/MinimaxSpectrum.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
/-
# The Noise-Floor Principle, Part VI: the minimax spectrum

Round-6 hypothesis closure, Phase A, cycle 3.

Parts I–V computed the noise floor of a *given* spectrum.  Here we solve the
adversarial problem: among all nonnegative spectra of prescribed total signal
energy `S` on `n` modes, which one is hardest to learn?

**Answer: the isotropic one.**  The floor is a concave, permutation-symmetric
functional of the spectrum, so it is maximised at the flat spectrum
`a i = S / n`, and the worst-case (minimax) irreducible risk is exactly

  `S b n / (S + n b)`  —  the harmonic combination of the signal energy `S`
                          and the saturation level `n b`.

Concretely: with little data (`n b ≫ S`) the minimax risk is `≈ S`, nothing is
learnable; with much data (`n b ≪ S`) it is `≈ n b`, one noise unit per mode.
The crossover is at `S = n b`, matching the per-mode threshold of Part II.

The engine is the *tangent-line trick* for the concave profile
`f x = x b /(x + b)`: `f x ≤ f c + f' c · (x - c)` with the exact remainder
`b² (x - c)² / ((c+b)² (x+b))`.

## Main results

* `tangent_bound`            — the tangent-line inequality with exact remainder
* `noiseFloor_le_flat`       — Jensen: no spectrum of energy `S` beats the flat one
* `noiseFloor_flat_value`    — the flat floor equals `S b n / (S + n b)`
* `isGreatest_noiseFloor_of_energy` — the minimax value, attained
* `minimax_le_min`           — the minimax risk is below both `S` and `n b`
* `effDim_sum_type`          — additivity of the effective dimension over a
                               direct sum of independent tasks
-/

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]






variable {a : ι → ℝ} {b S : ℝ}

theorem Catalog.MachineLearning.NoiseFloor.isGreatest_noiseFloor_of_energy[Nonempty ι] (hb : 0 < b) (hS0 : 0 ≤ S) :
    IsGreatest {r : ℝ | ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i = S) ∧ noiseFloor a b = r}
      (S * b * (Fintype.card ι : ℝ) / (S + (Fintype.card ι : ℝ) * b)) := by sorry
