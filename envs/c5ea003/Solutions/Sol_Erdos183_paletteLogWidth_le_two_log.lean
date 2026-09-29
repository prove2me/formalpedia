-- Prove2me | solution 1 for Erdos183.paletteLogWidth_le_two_log
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:29:11.707189+00:00
-- url     : https://prove2.me/submissions/7526f16a-1f40-4b62-929d-cb9b02fafe9a

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_Erdos183_one_le_log_nat_of_three_le

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution (H : ℕ) (hH : 3 ≤ H) :
    (paletteLogWidth H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
  have hlog : 1 ≤ Real.log (H : ℝ) :=
    one_le_log_nat_of_three_le H hH
  have hceil :
      (⌈Real.log (H : ℝ)⌉₊ : ℝ) ≤ Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log (H : ℝ))).le
  unfold paletteLogWidth
  by_cases htwo : 2 ≤ ⌈Real.log (H : ℝ)⌉₊
  · rw [max_eq_right htwo]
    linarith
  · rw [max_eq_left (by omega)]
    norm_num
    linarith
