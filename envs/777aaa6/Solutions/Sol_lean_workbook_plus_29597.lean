-- Prove2me | solution 1 for lean_workbook_plus_29597
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:10.733937+00:00
-- url     : https://prove2.me/submissions/fd56d6cb-fa1e-4047-9dd2-db39a6d7b365

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  (1111^2222 + 2222^3333 + 3333^4444) % 7 = 4 := by
  intros
  grind
