-- Prove2me | solution 1 for lean_workbook_plus_15893
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:49.68801+00:00
-- url     : https://prove2.me/submissions/66e3ebc4-3f3b-4fb9-9390-6b1485cc9d92

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :  ∀ a b c : ℝ, a * b + b * c + c * a ≤ 0 → a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c * (a + b + c) ≥ a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2) := by
  intro a b c
  intros
  nlinarith
