-- Prove2me | solution 1 for lean_workbook_plus_79821
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:46:20.001306+00:00
-- url     : https://prove2.me/submissions/f1bdd8d5-6383-473b-ba97-4a928a490480

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2014

theorem solution : (2014^((2014^2014) % 40)) % 110 = 56 := by
  norm_num
