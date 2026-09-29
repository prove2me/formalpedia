-- Prove2me | solution 1 for lean_workbook_plus_25647
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:15.244876+00:00
-- url     : https://prove2.me/submissions/3b3777cd-f67d-42ce-a67b-bfbd99e461b7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : (⌊x⌋ - 2 * ⌊x/2⌋) ≤ 1 := by
  have h : (((⌊x⌋ - 2 * ⌊x / 2⌋ : ℤ) : ℝ)) < 2 := by
    push_cast
    linarith [Int.floor_le x, Int.lt_floor_add_one (x / 2)]
  have h' : (⌊x⌋ - 2 * ⌊x / 2⌋ : ℤ) < 2 := by exact_mod_cast h
  omega
