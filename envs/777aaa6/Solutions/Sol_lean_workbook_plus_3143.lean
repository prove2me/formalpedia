-- Prove2me | solution 1 for lean_workbook_plus_3143
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:35.153381+00:00
-- url     : https://prove2.me/submissions/f101da35-708a-4880-9a87-b383516b996d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : |x - 2*y + z| ≤ |x-y| + |z-y| := by
  intros
  grind
