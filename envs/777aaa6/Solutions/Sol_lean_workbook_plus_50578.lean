-- Prove2me | solution 1 for lean_workbook_plus_50578
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:03.075025+00:00
-- url     : https://prove2.me/submissions/f0f1462a-6489-496a-ab53-fb017123e0dd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z: ℝ) (hx: x + y + z = 0): (x^2 + y^2 + z^2) / 2 * (x^5 + y^5 + z^5) / 5 = (x^7 + y^7 + z^7) / 7 := by
  intros
  grind
