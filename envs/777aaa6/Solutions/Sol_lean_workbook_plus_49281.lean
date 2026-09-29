-- Prove2me | solution 1 for lean_workbook_plus_49281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:19:26.374224+00:00
-- url     : https://prove2.me/submissions/ef43e9a0-c0c9-4260-9b5b-3060bc4e0637

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (α β : ℝ) (h₁ : α^3 - 3 * α^2 + 5 * α = 1) (h₂ : β^3 - 3 * β^2 + 5 * β = 5) : α + β = 2 := by
  have hq : 0 < (α-1)^2-(α-1)*(β-1)+(β-1)^2+2 := by nlinarith [sq_nonneg (α-β), sq_nonneg (α-1), sq_nonneg (β-1)]
  have he : (α+β-2)*((α-1)^2-(α-1)*(β-1)+(β-1)^2+2) = 0 := by nlinarith [h₁, h₂]
  have hz := (mul_eq_zero.mp he).resolve_right (ne_of_gt hq)
  linarith
