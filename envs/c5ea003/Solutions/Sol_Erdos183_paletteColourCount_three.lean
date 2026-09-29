-- Prove2me | solution 1 for Erdos183.paletteColourCount_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:32:19.26086+00:00
-- url     : https://prove2.me/submissions/2e9f59f5-4a6e-4c20-b78e-b898d99660d2

import Definitions.Def_erdos183_core
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution : paletteColourCount 3 = 342 := by
  have hlo : (1 : ℝ) < Real.log 3 := by
    nlinarith [Real.log_three_gt_d9]
  have hhi : Real.log (3 : ℝ) < 7 / 6 := by
    nlinarith [Real.log_three_lt_d9]
  have ha : ⌈Real.log (3 : ℝ)⌉₊ = 2 := by
    apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr
    constructor <;> norm_num <;> linarith
  have hm : ⌈(6 : ℝ) * Real.log (3 : ℝ)⌉₊ = 7 := by
    apply (Nat.ceil_eq_iff (by norm_num : (7 : ℕ) ≠ 0)).mpr
    constructor <;> norm_num <;> nlinarith
  norm_num [paletteColourCount, paletteLogWidth,
    saturatedMatrixRows, saturatedMatrixWidth, ha, hm]
