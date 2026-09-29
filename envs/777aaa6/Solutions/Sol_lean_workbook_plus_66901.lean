-- Prove2me | solution 1 for lean_workbook_plus_66901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:00.855812+00:00
-- url     : https://prove2.me/submissions/d353e67f-e80e-443b-a348-6ea89a883977

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) : (n * (n + 1)) / 2 < (2 * n + 1)^2 := by
  intros
  grind
