-- Prove2me | solution 1 for lean_workbook_plus_35564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:53.833566+00:00
-- url     : https://prove2.me/submissions/0f57c99a-d03d-4754-9b27-23f1b1e5eaef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (k : ℤ) (h : k > 0) : 2 ≡ k^2 [ZMOD k^2 - 2] := by
  intros
  exact?
