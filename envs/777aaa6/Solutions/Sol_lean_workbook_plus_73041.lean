-- Prove2me | solution 1 for lean_workbook_plus_73041
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:50.944773+00:00
-- url     : https://prove2.me/submissions/d9c069f7-0dd7-42c8-ae11-bdfe37edf1ec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) : 2 * Real.sqrt 7 - 4 ≤ k ∧ k ≤ 2 ↔ ↑2 * Real.sqrt 7 - 4 ≤ k ∧ k ≤ ↑2 := by
  norm_num
