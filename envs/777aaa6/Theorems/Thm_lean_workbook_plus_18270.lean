-- Prove2me | Theorems.Thm_lean_workbook_plus_18270
-- name    : lean_workbook_plus_18270
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0eb15bf5-1483-4ad6-b980-53fca6190ee5
-- statement:
--   For every $ n\in N$ , prove that \n\n $ \frac{3}{1!+2!+3!}+\frac{4}{2!+3!+4!}+...+\frac{n+2}{n!+(n+1)!+(n+2)!}<\frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18270 : ∀ n : ℕ, (∑ k in Finset.Icc 1 n, (k + 2) / (k! + (k + 1)! + (k + 2)!)) < 1 / 2   :=  by sorry
