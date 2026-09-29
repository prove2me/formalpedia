-- Prove2me | Theorems.Thm_lean_workbook_plus_67407
-- name    : lean_workbook_plus_67407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/87f811c6-23f3-4f26-bc18-ec24825b8255
-- statement:
--   We have given three positive real numbers $a,b,c$ satisfying the equation\n\n $(1) \;\; (a + c)(b^2 + ac) = 4a$ .\n\nEquation (1) is equivalent\n\n $(2) \;\; ca^2 + (b^2 + c^2 - 4)a + b^2c = 0$ .\n\nEquation (1) is a second degree equation in $a$ which is solvable iff its discriminant $D \geq 0$ , i.e.\n\n $D = (b^2 + c^2 - 4)^2 - (2bc)^2 \geq 0$ ,\n\nyielding\n\n $(3) \;\; |b^2 + c^2 - 4| \geq 2bc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67407  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : (a + c) * (b^2 + a * c) = 4 * a) :
  abs (b^2 + c^2 - 4) ≥ 2 * b * c   :=  by sorry
