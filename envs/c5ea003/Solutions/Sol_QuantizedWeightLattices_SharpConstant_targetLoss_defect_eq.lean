-- Prove2me | solution 1 for QuantizedWeightLattices.SharpConstant.targetLoss_defect_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:05:14.471506+00:00
-- url     : https://prove2.me/submissions/366e1190-70f0-4523-9161-cd7563bb3dee

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.SharpConstant Set Filter Topology in
theorem solution {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 3 ≤ n) :
    targetLoss δ (gridRound δ ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))))
        - ((1 - 1 / (n : ℝ)) * targetLoss δ (gridRound δ (δ / 2))
          + (1 / (n : ℝ)) * targetLoss δ (gridRound δ (-(δ / 2))))
      = δ * (1 - 1 / (n : ℝ)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- the three grid roundings: `δ/2 - δ/n ↦ 0`, `δ/2 ↦ δ`, `-δ/2 ↦ 0`
  have r1 : gridRound δ ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))) = 0 := by
    unfold gridRound
    have e : ((1 - 1 / (n : ℝ)) * (δ / 2) + (1 / (n : ℝ)) * (-(δ / 2))) / δ = 1 / 2 - 1 / n := by
      field_simp
      ring
    rw [e, round_eq]
    have : ⌊1 / 2 - 1 / (n : ℝ) + 1 / 2⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · have : 1 / (n : ℝ) ≤ 1 / 3 := by
          rw [div_le_div_iff₀ hn0 (by norm_num)]
          linarith
        linarith
      · have : 0 < 1 / (n : ℝ) := by positivity
        linarith
    rw [this]
    simp
  have r2 : gridRound δ (δ / 2) = δ := by
    unfold gridRound
    have e : δ / 2 / δ = 1 / 2 := by field_simp
    rw [e, round_eq]
    norm_num
  have r3 : gridRound δ (-(δ / 2)) = 0 := by
    unfold gridRound
    have e : -(δ / 2) / δ = -(1 / 2) := by field_simp
    rw [e, round_eq]
    norm_num
  rw [r1, r2, r3]
  unfold targetLoss
  rw [sub_self, abs_zero, zero_sub, abs_neg, abs_of_pos hδ]
  ring
