-- Prove2me | Theorems.Thm_lean_workbook_plus_63128
-- name    : lean_workbook_plus_63128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/07082443-d23e-4295-80cf-c6f4422635d6
-- statement:
--   Prove this: \n[m*x] + [n*x] <= [(m+n)*x]\nDo you mean: \\(\\lfloor m\\cdot x\\rfloor+\\lfloor n\\cdot x\\rfloor\\le\\lfloor(m+n)\\cdot x\\rfloor\\) where that's the greatest integer function?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63128 (m n x : ℝ) : (Int.floor (m * x) + Int.floor (n * x) : ℝ) ≤ Int.floor ((m + n) * x)   :=  by sorry
