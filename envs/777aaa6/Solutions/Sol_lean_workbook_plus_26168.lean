-- Prove2me | solution 1 for lean_workbook_plus_26168
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:54.767518+00:00
-- url     : https://prove2.me/submissions/43b8a774-72da-409e-aa58-437a0173e820

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 3^(4^5) + 4^(5^6) = (3^(4^4))^4 + 4 * (2^((5^6 - 1) / 2))^4 := by
  intros
  grind
