-- Prove2me | solution 1 for lean_workbook_plus_59348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:02.226322+00:00
-- url     : https://prove2.me/submissions/07cd11f3-4c36-4542-8d15-8fb618beab27

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : (18 + x) / (6 + 18 + 12 + x) = 3 / 5) :
  x = 9 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg x]
