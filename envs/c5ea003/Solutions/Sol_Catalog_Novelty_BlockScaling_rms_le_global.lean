-- Prove2me | solution 1 for Catalog.Novelty.BlockScaling.rms_le_global
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:20.674806+00:00
-- url     : https://prove2.me/submissions/42e4a872-178c-4631-9cfc-953728321b8f

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
theorem solution(r : Fin B → ℝ) (R : ℝ) (hB : 0 < B) (hR : ∀ i, r i ≤ R)
    (hr : ∀ i, 0 ≤ r i) : rms r ≤ R := by
  have hRnn : 0 ≤ R := le_trans (hr ⟨0, hB⟩) (hR ⟨0, hB⟩)
  have hsum : ∑ i, r i ^ 2 ≤ (B : ℝ) * R ^ 2 := by
    have : ∀ i ∈ Finset.univ, r i ^ 2 ≤ R ^ 2 := by
      intro i _
      exact pow_le_pow_left₀ (hr i) (hR i) 2
    calc ∑ i, r i ^ 2 ≤ ∑ _i : Fin B, R ^ 2 := Finset.sum_le_sum this
      _ = (B : ℝ) * R ^ 2 := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hBpos : (0:ℝ) < B := by exact_mod_cast hB
  have hmsq : msq r ≤ R ^ 2 := by
    rw [msq, div_le_iff₀ hBpos]
    linarith [hsum]
  calc rms r ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hmsq
    _ = R := Real.sqrt_sq hRnn
