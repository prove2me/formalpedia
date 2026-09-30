-- Prove2me | solution 1 for lean_workbook_plus_79816
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:46:19.131285+00:00
-- url     : https://prove2.me/submissions/a042ded5-0290-4961-b3b7-02ffdd670229

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1000

theorem solution : (100 + 1) ^ 1000 ≥ 1000 * 100 ^ 1000 := by
  norm_num
