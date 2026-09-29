-- Prove2me | solution 1 for lean_workbook_plus_38768
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:01.830825+00:00
-- url     : https://prove2.me/submissions/80049dd4-38d8-4609-921e-e260c716ceea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 4^500 ≡ 4^250 [ZMOD 12] := by
  intros
  rfl
