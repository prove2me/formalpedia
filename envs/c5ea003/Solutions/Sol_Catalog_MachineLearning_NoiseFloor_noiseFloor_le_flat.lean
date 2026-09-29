-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.noiseFloor_le_flat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:42:25.256822+00:00
-- url     : https://prove2.me/submissions/917343aa-04bb-4496-ab3e-9feaa60b7ab6

-- Sol generated from MachineLearning/NoiseFloor/MinimaxSpectrum.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_noiseFloor_eq_sum
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


/-- **Tangent-line bound with exact remainder.**  For the concave profile
`f x = x b / (x + b)` and any base point `c ≥ 0`,
`f x = f c + f' c (x - c) - b² (x-c)² / ((c+b)²(x+b))`. -/
lemma tangent_identity {x c b : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hb : 0 < b) :
    c * b / (c + b) + b ^ 2 / (c + b) ^ 2 * (x - c) - x * b / (x + b)
      = b ^ 2 * (x - c) ^ 2 / ((c + b) ^ 2 * (x + b)) := by
  have h1 : 0 < c + b := by linarith
  have h2 : 0 < x + b := by linarith
  field_simp
  ring

/-- The tangent-line inequality: a concave profile lies below its tangents. -/
lemma tangent_bound {x c b : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hb : 0 < b) :
    x * b / (x + b) ≤ c * b / (c + b) + b ^ 2 / (c + b) ^ 2 * (x - c) := by
  have h1 : 0 < c + b := by linarith
  have h2 : 0 < x + b := by linarith
  have hid := tangent_identity hx hc hb
  have hnn : 0 ≤ b ^ 2 * (x - c) ^ 2 / ((c + b) ^ 2 * (x + b)) := by positivity
  linarith



variable {a : ι → ℝ} {b S : ℝ}











open Catalog.MachineLearning.NoiseFloor in
theorem solution[Nonempty ι] (ha : ∀ i, 0 ≤ a i) (hb : 0 < b)
    (hS : ∑ i, a i = S) :
    noiseFloor a b ≤ (Fintype.card ι : ℝ) * ((S / Fintype.card ι) * b /
      (S / Fintype.card ι + b)) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun i _ => ha i
  set c : ℝ := S / (Fintype.card ι : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hstep : noiseFloor a b
      ≤ ∑ _i : ι, (c * b / (c + b)) + b ^ 2 / (c + b) ^ 2 * (∑ i, a i - (Fintype.card ι : ℝ) * c) := by
    rw [noiseFloor_eq_sum]
    have := Finset.sum_le_sum
      (fun i (_ : i ∈ univ) => tangent_bound (ha i) hc0 hb (x := a i) (c := c))
    calc ∑ i, a i * b / (a i + b)
        ≤ ∑ i, (c * b / (c + b) + b ^ 2 / (c + b) ^ 2 * (a i - c)) := this
      _ = ∑ _i : ι, (c * b / (c + b))
            + b ^ 2 / (c + b) ^ 2 * (∑ i, a i - (Fintype.card ι : ℝ) * c) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
            Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Finset.sum_const,
            nsmul_eq_mul, Finset.card_univ]
  have hzero : ∑ i, a i - (Fintype.card ι : ℝ) * c = 0 := by
    rw [hS, hc]
    field_simp
    ring
  rw [hzero, mul_zero, add_zero, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hstep
  exact hstep
