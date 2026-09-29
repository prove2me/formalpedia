-- Prove2me | solution 1 for lean_workbook_plus_13339
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:28.396683+00:00
-- url     : https://prove2.me/submissions/13c4569e-954d-4611-b8c8-52be400661db

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 2^(2018) + (2^(2018) * (2^(2019) - 1)) = 2^(4037) := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
