-- Prove2me | solution 1 for lean_workbook_plus_46832
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:05.936717+00:00
-- url     : https://prove2.me/submissions/1ef14b9e-e715-48f0-8533-934cd788433d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 2 ^ 1000 ≡ 2 [MOD 7] := by
  intros
  rfl
