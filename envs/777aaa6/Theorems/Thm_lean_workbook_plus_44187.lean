-- Prove2me | Theorems.Thm_lean_workbook_plus_44187
-- name    : lean_workbook_plus_44187
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6320b51a-e552-48bb-b09d-9deac97f33b3
-- statement:
--   We work backwards. Let the amount of money before entering the third store be $x$ . Then $x-(0.6x+6)=2$ , so $x=\frac{2+6}{1-0.6}=20$ dollars. Similarly, the amount of money before entering the second store is $\frac{20+5}{1-0.5}=50$ dollars and the amount of money before entering the first store is $\frac{50+4}{1-0.4}=\boxed{90}$ dollars.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44187  (x y z : ℝ)
  (h₀ : x - (0.6 * x + 6) = 2)
  (h₁ : y - (0.5 * y + 5) = x)
  (h₂ : z - (0.4 * z + 4) = y) :
  z = 90   :=  by sorry
