-- Prove2me | solution 1 for lean_workbook_plus_44363
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:19.982882+00:00
-- url     : https://prove2.me/submissions/1a54d6c5-350a-4619-ae3c-bc26809fac82

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (h : a * b * c * (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a ^ 3 * b ^ 3 * c ^ 3) : a * b * c = 0 ∨ (a ^ 2 - a * b + b ^ 2) * (b ^ 2 - b * c + c ^ 2) * (c ^ 2 - c * a + a ^ 2) = a ^ 2 * b ^ 2 * c ^ 2 := by
  intros
  grind
