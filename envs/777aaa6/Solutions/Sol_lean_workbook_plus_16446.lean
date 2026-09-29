-- Prove2me | solution 1 for lean_workbook_plus_16446
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:34.409546+00:00
-- url     : https://prove2.me/submissions/c7b2f9af-0846-4fd4-ad07-351886777d83

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  (1998^1999 + 1999^1998) % 7 = 4 := by
  intros
  grind
