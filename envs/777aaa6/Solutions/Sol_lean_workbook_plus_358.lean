-- Prove2me | solution 1 for lean_workbook_plus_358
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:18.40665+00:00
-- url     : https://prove2.me/submissions/08108d6e-b971-49d3-a7f8-4ff7496d704d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℤ) : 13 ≤ |2*x - 7| + |2*x - 9| + |2*x - 11| + |2*x - 13| + |2*x - 15| := by
  intros
  grind
