-- Prove2me | solution 1 for Catalog.Novelty.QuantCurvature.curvatureBound_convex_discrete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:18:50.824904+00:00
-- url     : https://prove2.me/submissions/ffae9f0b-bc53-432f-aa2c-6881988d3af7

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
theorem solution{K : ℝ} (hK : 0 < K) (b : ℕ) :
    2 * curvatureBound K (b + 1) < curvatureBound K b + curvatureBound K (b + 2) := by
  have h4 : (0:ℝ) < 4 ^ b := by positivity
  have e0 : curvatureBound K b = K / 4 ^ b := rfl
  have e1 : curvatureBound K (b + 1) = K / (4 ^ b * 4) := by
    simp [curvatureBound, pow_succ]
  have e2 : curvatureBound K (b + 2) = K / (4 ^ b * 16) := by
    simp [curvatureBound, pow_succ]
    ring_nf
  rw [e0, e1, e2]
  have key : K / 4 ^ b + K / (4 ^ b * 16) - 2 * (K / (4 ^ b * 4)) = 9 * K / (16 * 4 ^ b) := by
    field_simp
    ring
  have hpos : 0 < 9 * K / (16 * 4 ^ b) := by positivity
  linarith [key, hpos]
