-- Prove2me | solution 1 for Catalog.MachineLearning.NoiseFloor.ridge_can_be_arbitrarily_worse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:44:08.673193+00:00
-- url     : https://prove2.me/submissions/584f43f2-782a-4038-9b14-faee714ce080

-- Sol generated from MachineLearning/NoiseFloor/EarlyStopping.lean
import Mathlib
import Definitions.Def_MachineLearning_NoiseFloor_EarlyStopping
import Definitions.Def_MachineLearning_NoiseFloor_EffectiveDimension
import Definitions.Def_MachineLearning_NoiseFloor_NoiseFloorPrinciple
import Theorems.Thm_Catalog_MachineLearning_NoiseFloor_exp_twenty_large
/-
# The Noise-Floor Principle, Part VII: early stopping versus ridge

Round-6 hypothesis closure, Phase A, cycle 4.

Gradient flow on a quadratic loss with data covariance spectrum `mu`, stopped at
time `tau`, is the spectral filter

  `gradFlowFilter mu tau i = 1 - exp (- mu i * tau)`,

the continuous-time idealisation of early stopping.  Folklore says "early
stopping is ridge with `lam = 1/tau`".  We make the folklore precise **and show
it is one-sided**:

* `gradFlow_le_four_mul_ridge` — early stopping at time `tau` is never worse
  than four times the matched ridge `lam = 1/tau`, for every spectrum, every
  signal and every noise level;
* `ridge_can_be_arbitrarily_worse` — the converse fails badly: on an explicit
  one-mode problem the matched ridge costs more than `100×` early stopping.

Both filters obey the Part II floor (`gradFlow_ge_noiseFloor`), so the
comparison is a statement about *how* the two families approach the same
irreducible limit: the exponential filter kills the bias of well-conditioned
modes at an exponential rate, while ridge only kills it polynomially.

## Main results

* `one_sub_exp_le_two_mul`   — `1 - e^{-u} ≤ 2u/(1+u)` (uniform in `u ≥ 0`)
* `exp_neg_le_one_div`       — `e^{-u} ≤ 1/(1+u)`
* `gradFlow_le_four_mul_ridge`, `gradFlow_ge_noiseFloor`
* `ridge_can_be_arbitrarily_worse`
-/

open Catalog.MachineLearning.NoiseFloor

open Finset

variable {ι : Type*} [Fintype ι]









variable {a mu : ι → ℝ} {b tau : ℝ}










open Catalog.MachineLearning.NoiseFloor in
theorem solution:
    100 * filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (gradFlowFilter (fun _ => 1) 10)
      ≤ filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (ridgeFilter (fun _ => 1) (1 / 10)) := by
  have hgf : filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (gradFlowFilter (fun _ => 1) 10)
      = Real.exp 20 * (Real.exp (-(1 * 10))) ^ 2 + 1 * (1 - Real.exp (-(1 * 10))) ^ 2 := by
    rw [filterRisk]
    simp only [Finset.univ_unique, Finset.sum_singleton, gradFlowFilter]
    ring_nf
  have hridge : filterRisk (fun _ : Fin 1 => Real.exp 20) 1 (ridgeFilter (fun _ => 1) (1 / 10))
      = Real.exp 20 * (1 - (1 : ℝ) / (1 + 1 / 10)) ^ 2 + 1 * ((1 : ℝ) / (1 + 1 / 10)) ^ 2 := by
    rw [filterRisk]
    simp only [Finset.univ_unique, Finset.sum_singleton, ridgeFilter]
  rw [hgf, hridge]
  have hexp10 : Real.exp (-(1 * 10)) = (Real.exp 20)⁻¹ * Real.exp 10 := by
    rw [← Real.exp_neg]
    rw [← Real.exp_add]
    norm_num
  have hpos20 : (0 : ℝ) < Real.exp 20 := Real.exp_pos _
  have hpos10 : (0 : ℝ) < Real.exp 10 := Real.exp_pos _
  have hsq : Real.exp 20 * (Real.exp (-(1 * 10))) ^ 2 = 1 := by
    rw [show (-(1 * 10) : ℝ) = -10 by norm_num, ← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (-10) = -20 by norm_num, Real.exp_neg]
    field_simp
  have hbound : (1 : ℝ) - Real.exp (-(1 * 10)) ≤ 1 := by
    have := Real.exp_pos (-(1 * 10))
    linarith
  have hbound0 : (0 : ℝ) ≤ 1 - Real.exp (-(1 * 10)) := by
    have : Real.exp (-(1 * 10)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    linarith
  have hgfle : Real.exp 20 * (Real.exp (-(1 * 10))) ^ 2 + 1 * (1 - Real.exp (-(1 * 10))) ^ 2
      ≤ 2 := by
    rw [hsq]
    nlinarith
  have hridgege : (200 : ℝ)
      ≤ Real.exp 20 * (1 - (1 : ℝ) / (1 + 1 / 10)) ^ 2 + 1 * ((1 : ℝ) / (1 + 1 / 10)) ^ 2 := by
    have hcoef : (1 - (1 : ℝ) / (1 + 1 / 10)) ^ 2 = 1 / 121 := by norm_num
    rw [hcoef]
    have := exp_twenty_large
    nlinarith [sq_nonneg ((1 : ℝ) / (1 + 1 / 10))]
  calc 100 * (Real.exp 20 * (Real.exp (-(1 * 10))) ^ 2 + 1 * (1 - Real.exp (-(1 * 10))) ^ 2)
      ≤ 100 * 2 := mul_le_mul_of_nonneg_left hgfle (by norm_num)
    _ ≤ Real.exp 20 * (1 - (1 : ℝ) / (1 + 1 / 10)) ^ 2 + 1 * ((1 : ℝ) / (1 + 1 / 10)) ^ 2 := by
        norm_num at hridgege ⊢
        linarith
