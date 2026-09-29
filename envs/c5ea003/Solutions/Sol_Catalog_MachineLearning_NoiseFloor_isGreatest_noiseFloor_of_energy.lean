-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.isGreatest_noiseFloor_of_energy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:43:59.379804+00:00
-- url     : https://prove2.me/submissions/a1e019dc-6bb5-4ae6-87c7-d927c46c5f5d

-- Sol generated from MachineLearning/NoiseFloor/MinimaxSpectrum.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_noiseFloor_eq_sum
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_noiseFloor_le_flat
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


/-- The flat spectrum of energy `S` realises the value `S b n / (S + n b)`. -/
theorem noiseFloor_flat_value [Nonempty ι] (hb : 0 < b) (hS0 : 0 ≤ S) :
    noiseFloor (fun _ : ι => S / (Fintype.card ι : ℝ)) b
      = S * b * (Fintype.card ι : ℝ) / (S + (Fintype.card ι : ℝ) * b) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden : 0 < S + (Fintype.card ι : ℝ) * b := by positivity
  rw [noiseFloor_eq_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hd : S / (Fintype.card ι : ℝ) + b > 0 := by positivity
  field_simp









open Catalog.MachineLearning.NoiseFloor in
theorem solution[Nonempty ι] (hb : 0 < b) (hS0 : 0 ≤ S) :
    IsGreatest {r : ℝ | ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i = S) ∧ noiseFloor a b = r}
      (S * b * (Fintype.card ι : ℝ) / (S + (Fintype.card ι : ℝ) * b)) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · refine ⟨fun _ => S / (Fintype.card ι : ℝ), fun i => by positivity, ?_, ?_⟩
    · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp
    · exact noiseFloor_flat_value hb hS0
  · rintro r ⟨a, ha, hsum, rfl⟩
    have h := noiseFloor_le_flat ha hb hsum
    have hval := noiseFloor_flat_value (ι := ι) hb hS0
    rw [noiseFloor_eq_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hval
    rw [← hval]
    exact h
