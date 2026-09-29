-- Prove2me | solution 1 for lean_workbook_plus_69666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:29.020383+00:00
-- url     : https://prove2.me/submissions/9b7bef20-d741-45e8-a59c-f75dd15c110c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 2 ^ 999 ≡ 2 ^ 19 [MOD 100] := by
  intros
  rfl
