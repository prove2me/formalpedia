-- Prove2me | solution 1 for lean_workbook_plus_12482
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:52.285358+00:00
-- url     : https://prove2.me/submissions/bde8e9d4-b37e-45cf-9d70-151f1666dee6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 2 ^ 1000 ≡ 1 [ZMOD 3] := by
  intros
  rfl
