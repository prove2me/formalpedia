-- Prove2me | solution 1 for Catalog.Novelty.BlockScaling.scaleGain_eq_sqrt_card_of_single_outlier
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:21.263177+00:00
-- url     : https://prove2.me/submissions/6eedfdc4-b899-4a38-98e6-b11bbbb05ab7

-- Sol generated from Novelty/BlockScalingBitGain.lean
import Mathlib
import Definitions.Def_Novelty_BlockScalingBitGain
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

open Catalog.Novelty.BlockScaling

open Finset

variable {B : ℕ}














open Catalog.Novelty.BlockScaling in
theorem solution(R : ℝ) (hR : 0 < R) (i₀ : Fin B) :
    scaleGain (fun i => if i = i₀ then R else 0) R = Real.sqrt B := by
  have hBpos : (0:ℝ) < B := by
    have : 0 < B := Fin.pos i₀
    exact_mod_cast this
  have hsum : ∑ i, (if i = i₀ then R else 0) ^ 2 = R ^ 2 := by
    simp [apply_ite (fun x : ℝ => x ^ 2)]
  have hmsq : msq (fun i => if i = i₀ then R else 0) = R ^ 2 / B := by
    rw [msq, hsum]
  have hrms : rms (fun i => if i = i₀ then R else 0) = R / Real.sqrt B := by
    rw [rms, hmsq, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hR.le]
  have hs : Real.sqrt ((B : ℕ) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hBpos)
  rw [scaleGain, hrms]
  field_simp
