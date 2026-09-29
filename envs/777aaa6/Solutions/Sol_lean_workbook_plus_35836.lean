-- Prove2me | solution 1 for lean_workbook_plus_35836
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:29.057172+00:00
-- url     : https://prove2.me/submissions/06c70c08-ad15-4fac-836b-e7a899e5fb49

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution y x :  x^2 + 200 * x + 1 = y^2 → 100^2 - 1 = (x + 100)^2 - y^2 := by
  intros
  grind
