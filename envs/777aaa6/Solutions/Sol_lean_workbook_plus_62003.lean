-- Prove2me | solution 1 for lean_workbook_plus_62003
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:18.996016+00:00
-- url     : https://prove2.me/submissions/d35ccf25-5727-4128-9974-6912c8b467d5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  ∀ a b c : ℝ, a^2 + b^2 + c^2 + 2 * a * b * c = 1 → (a + b * c) * (b + a * c) * (c + a * b) = (1 - a^2) * (1 - b^2) * (1 - c^2) := by
  intro a b c
  intros
  nlinarith
