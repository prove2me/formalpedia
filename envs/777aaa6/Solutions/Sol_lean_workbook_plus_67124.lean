-- Prove2me | solution 1 for lean_workbook_plus_67124
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:20.307357+00:00
-- url     : https://prove2.me/submissions/2d250791-b701-4a69-a28d-b25a6b76819f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 3 ^ 1000 ≡ 1 [ZMOD 10000] := by
  intros
  rfl
