-- Prove2me | solution 1 for lean_workbook_plus_32820
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:46.215387+00:00
-- url     : https://prove2.me/submissions/9d5cbd7c-b8ce-4459-a09b-3fd9b662a6d7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (a + b + c) ^ 2 ≥ a + b + c + a * b + b * c + c * a ↔ a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ a + b + c := by
  intros
  grind
