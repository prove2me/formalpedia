-- Prove2me | solution 1 for Catalog.Novelty.QuantCurvature.quadExcess_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:18:52.718272+00:00
-- url     : https://prove2.me/submissions/c535a11e-b124-45cf-b0ad-765057319491

-- Sol generated from Novelty/QuantCurvatureNoFloor.lean
import Mathlib
import Definitions.Def_Novelty_QuantCurvatureNoFloor
import Definitions.Def_Novelty_WeightQuantFloorLadder

/-!
# Curvature explains the weight ladder: a `4`-per-bit ceiling and no intrinsic floor

Companion to `Novelty.WeightQuantFloorLadder` (NET-95).  The measured k-quant
ladder obeys a geometric law with per-bit factor in `[5/2, 3]`.  This file gives
the structural model that *predicts* such a law, and proves the two statements
that dissolve the alleged "sub-6-bit floor".

**The model.**  Near a trained optimum the loss increase caused by a weight
perturbation `e` is, to second order, the quadratic form
`quadExcess lam e = ½ ∑ᵢ λᵢ eᵢ²` in the Hessian eigenbasis.  A `b`-bit quantiser
with dynamic-range constant `c` produces `|eᵢ| ≤ c / 2 ^ b`.  Hence

  `quadExcess ≤ (n Λ c² / 2) / 4 ^ b = curvatureBound K b`.

**Two consequences.**

* `curvatureBound_per_bit` — the model's degradation is multiplied by *exactly*
  `4` per bit removed.  So `4` is the theoretical ceiling of the per-bit rate,
  and `measured_ladder_beats_curvature_ceiling` records that the measured ladder
  stays strictly below it at every pair of rungs (observed rates `2.54`–`2.98`):
  calibration-aware k-quants beat the naive curvature prediction.
* `quantizer_quality_is_a_bit_shift` — a quantiser that is `2 ^ j` times more
  accurate is worth *exactly* `j` bits: the degradation bound at bit width `b`
  with constant `c / 2 ^ j` equals the bound at width `b + j` with constant `c`.
  Combined with `no_intrinsic_floor` (for any bit width and any tolerance there
  is a quantiser quality meeting the tolerance *at that width*) this is the NET-95
  law in formal form: **the floor is a property of (quantiser quality × scale),
  never of the bit width alone.**

Finally `curvatureBound_convexOn` shows the model curve is convex in the bit
width — the "gentle convex curve" of the measurement — and `no_bit_width_floor`
shows that in this model no finite bit width is undeployable.
-/

open Catalog.Novelty.QuantCurvature

open Finset Catalog.Novelty.WeightQuantFloor

/-! ## 1. The second-order model -/





/-! ## 2. The `4`-per-bit ceiling -/






/-! ## 3. Quantiser quality is a bit shift -/



/-! ## 4. The measurement versus the ceiling -/



open Catalog.Novelty.QuantCurvature in
theorem solution{n : ℕ} (lam e : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    0 ≤ quadExcess lam e := by
  have : 0 ≤ ∑ i, lam i * e i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
  simpa [quadExcess] using by linarith
