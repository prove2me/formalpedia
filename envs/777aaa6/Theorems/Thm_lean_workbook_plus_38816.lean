-- Prove2me | Theorems.Thm_lean_workbook_plus_38816
-- name    : lean_workbook_plus_38816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7d817230-883f-4dae-aa10-7638e79e3b0b
-- statement:
--   since $A+B+C=180^{\circ}$ (what is because A, B, C are the angles of a triangle) yields\n$\left(90^{\circ}-\frac{A}{2}\right)+\left(90^{\circ}-\frac{B}{2}\right)+\left(90^{\circ}-\frac{C}{2}\right)=270^{\circ}-\frac{A+B+C}{2}$\n$=270^{\circ}-\frac{180^{\circ}}{2}=180^{\circ}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38816 :
  ∀ A B C : ℝ, A + B + C = 180 → (90 - A / 2) + (90 - B / 2) + (90 - C / 2) = 180   :=  by sorry
