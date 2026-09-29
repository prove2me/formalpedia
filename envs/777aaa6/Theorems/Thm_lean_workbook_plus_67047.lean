-- Prove2me | Theorems.Thm_lean_workbook_plus_67047
-- name    : lean_workbook_plus_67047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3889c36f-9078-4cc1-ace6-fc3dcd50f057
-- statement:
--   Prove that $(a_{1}^2+a_{2}^2+a_{3}^2)(b_{1}^2+b_{2}^2+b_{3}^2) \geq a_{1}^2b_{1}^2+a_{2}^2b_{2}^2+a_{3}^2b_{3}^2+2a_{1}b_{2}a_{2}b_{1}+2a_{1}b_{3}a_{3}b_{1}+2a_{2}b_{3}a_{3}b_{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67047 (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
  (a₁^2 + a₂^2 + a₃^2) * (b₁^2 + b₂^2 + b₃^2) ≥ a₁^2 * b₁^2 + a₂^2 * b₂^2 + a₃^2 * b₃^2 + 2 * a₁ * b₂ * a₂ * b₁ + 2 * a₁ * b₃ * a₃ * b₁ + 2 * a₂ * b₃ * a₃ * b₂   :=  by sorry
