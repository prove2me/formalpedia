-- Prove2me | solution 1 for lean_workbook_plus_24600
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:33.562803+00:00
-- url     : https://prove2.me/submissions/2cc3f27b-9e43-4538-8bd5-e12378877872

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  (7^4)^502 * 7^2 ≡ 49 [MOD 100] := by
  intros
  rfl
