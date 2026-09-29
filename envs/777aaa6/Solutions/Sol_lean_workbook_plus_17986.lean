-- Prove2me | solution 1 for lean_workbook_plus_17986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:18:01.549691+00:00
-- url     : https://prove2.me/submissions/e9175134-97e3-45ae-89a7-36c9fc065903

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b : ℝ, a^4 + b^4 + 4 * a^2 * b^2 ≥ 3 * a * b * (a^2 + b^2) := by
  intro a b
  intros
  simp_all <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
