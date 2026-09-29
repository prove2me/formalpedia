-- Prove2me | Definitions.Def_Novelty_BlockScalingBitGain
-- name    : Novelty_BlockScalingBitGain
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:17.493724+00:00
-- url     : https://prove2.me/theorems/e78f7ee2-f720-4492-afef-9b6ce7a52d26
-- title:
--   Aether Catalog definitions — Novelty_BlockScalingBitGain
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BlockScalingBitGain`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BlockScalingBitGain.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_WeightQuantFloorLadder

/-!
# Separating quantiser quality from scale: block scaling is worth `log₂ (R / rms)` bits

Cycle 3 of the NET-95 thread.  The measurement's own "honest limits" section flags
a confound: the toy sub-6-bit floor (NET-52, round-to-nearest with a *single*
tensor-wide scale) versus the k-quant ladder that stays deployable to 2.6 bpw
crosses **quantiser quality and model scale simultaneously**.  This file removes
the qualitative part of that confound by computing, exactly, what the *quality*
half is worth.

**Model.**  Split a tensor into `B` blocks; let `r i` be the dynamic range of
block `i` and `R = maxᵢ r i` the tensor-wide range.  A `b`-bit uniform quantiser
with one global scale has per-coordinate error proportional to `R / 2 ^ b`; with a
per-block scale, block `i` has error proportional to `r i / 2 ^ b`, so the mean
square error is governed by `rms r` in place of `R`.  Define the **scale gain**
`scaleGain r R = R / rms r`.

**Results.**

* `one_le_scaleGain` — block scaling never hurts: `scaleGain ≥ 1`.
* `scaleGain_le_sqrt_card` — and it can never be worth more than `√B`.
* `scaleGain_eq_sqrt_card_of_single_outlier` — the bound is attained exactly when
  the tensor's range is carried by one block: outlier concentration is the *whole*
  source of the gain.
* `block_scaling_is_a_bit_shift` — a gain of `2 ^ j` moves the entire degradation
  curve by exactly `j` bits (matching `quantizer_quality_is_a_bit_shift` in
  `Novelty.QuantCurvatureNoFloor`).  So "quality" is measured in bits and is
  directly comparable with "bit width": the two axes of the confound live in the
  same units.
* `k_quant_block_budget` — at the k-quant block size `B = 256` the entire budget
  is `√256 = 16 = 2 ^ 4`, i.e. **at most 4 bits**; and
  `observed_floor_shift_within_block_budget` records that the measured floor shift
  (6.0 bpw → 2.6 bpw, i.e. 3.4 bits) fits inside that budget, so the collapse of
  the floor needs no appeal to scale at all — quantiser quality alone can account
  for it.  This turns the documented confound into a falsifiable prediction: an
  RTN-vs-k-quant comparison at *fixed* scale should show a shift of at most 4
  bits, and of exactly `log₂ (R / rms r)` bits for the measured range profile.
-/

namespace Catalog.Novelty.BlockScaling

open Finset

variable {B : ℕ}

/-- Mean square of the per-block dynamic ranges. -/
noncomputable def msq (r : Fin B → ℝ) : ℝ := (∑ i, r i ^ 2) / B

/-- Root mean square of the per-block dynamic ranges: the effective range seen by
a per-block quantiser. -/
noncomputable def rms (r : Fin B → ℝ) : ℝ := Real.sqrt (msq r)

/-- The scale gain of block quantisation: the factor by which the effective
dynamic range shrinks when a tensor-wide scale `R` is replaced by per-block
scales. -/
noncomputable def scaleGain (r : Fin B → ℝ) (R : ℝ) : ℝ := R / rms r










end Catalog.Novelty.BlockScaling


