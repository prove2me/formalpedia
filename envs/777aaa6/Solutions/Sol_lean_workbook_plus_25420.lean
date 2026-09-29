-- Prove2me | solution 1 for lean_workbook_plus_25420
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:33.626391+00:00
-- url     : https://prove2.me/submissions/a91fb637-374a-4d73-977e-382803a5cfeb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (w : ℂ) (hw : w ^ 3 = 1) (hw' : w ≠ 1) : w ^ 5 + w + 1 = 0 := by
  intros
  grind
