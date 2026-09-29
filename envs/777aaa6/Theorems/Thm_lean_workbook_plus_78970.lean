-- Prove2me | Theorems.Thm_lean_workbook_plus_78970
-- name    : lean_workbook_plus_78970
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/915e1fc5-b9f9-4a97-b256-f4be27e3c915
-- statement:
--   If $y=\sin (x+\frac{\pi }{4})$ then $\sin{2x}=2y^2-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78970 (x y : ℝ) (h₁ : y = Real.sin (x + Real.pi / 4)) : Real.sin (2 * x) = 2 * y ^ 2 - 1   :=  by sorry
