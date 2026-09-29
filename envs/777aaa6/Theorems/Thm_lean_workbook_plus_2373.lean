-- Prove2me | Theorems.Thm_lean_workbook_plus_2373
-- name    : lean_workbook_plus_2373
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3312f553-46f3-4643-8b05-0ca700ca1f11
-- statement:
--   Prove that $\frac{n+2}{n!+(n+1)!+(n+2)!}=\frac{1}{(n+1)!}-\frac{1}{(n+2)!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2373 : ∀ n : ℕ, (n + 2) / (n! + (n + 1)! + (n + 2)!) = 1 / (n + 1)! - 1 / (n + 2)!   :=  by sorry
