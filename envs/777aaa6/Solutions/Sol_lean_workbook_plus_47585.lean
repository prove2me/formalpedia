-- Prove2me | solution 1 for lean_workbook_plus_47585
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:56.124299+00:00
-- url     : https://prove2.me/submissions/10050133-0fc2-46cd-aa81-d7453dbc9a3b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 5 + Real.sqrt 9 + 1084 + 197495 + 17237 + 1753 = 217577 := by
  intros
  norm_num at *
