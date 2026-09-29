-- Prove2me | Definitions.Def_Novelty_QuantCurvatureNoFloor
-- name    : Novelty_QuantCurvatureNoFloor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:37:47.82971+00:00
-- url     : https://prove2.me/theorems/14431706-3049-4d4d-a4ea-c94dc01a6ba4
-- title:
--   Aether Catalog definitions — Novelty_QuantCurvatureNoFloor
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.QuantCurvatureNoFloor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/QuantCurvatureNoFloor.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Novelty.QuantCurvature

open Finset Catalog.Novelty.WeightQuantFloor

/-! ## 1. The second-order model -/

/-- Second-order (Hessian) model of the loss increase caused by a weight
perturbation `e`, written in the Hessian eigenbasis with eigenvalues `lam`. -/
noncomputable def quadExcess {n : ℕ} (lam e : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, lam i * e i ^ 2


/-- The degradation bound predicted by curvature: `K / 4 ^ b` at `b` bits. -/
noncomputable def curvatureBound (K : ℝ) (b : ℕ) : ℝ := K / 4 ^ b


/-! ## 2. The `4`-per-bit ceiling -/






/-! ## 3. Quantiser quality is a bit shift -/



/-! ## 4. The measurement versus the ceiling -/


end Catalog.Novelty.QuantCurvature


