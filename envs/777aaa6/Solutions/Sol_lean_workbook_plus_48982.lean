-- Prove2me | solution 1 for lean_workbook_plus_48982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:44.862533+00:00
-- url     : https://prove2.me/submissions/84935809-dd26-4d87-89fd-bd72163f8a2a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  1 - (Real.sqrt 3 / 2)^2 = 1 / 4 := by
  intros
  grind
