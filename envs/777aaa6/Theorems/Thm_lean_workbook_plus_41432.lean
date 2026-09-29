-- Prove2me | Theorems.Thm_lean_workbook_plus_41432
-- name    : lean_workbook_plus_41432
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e0df1870-b4f3-4cef-b6f0-4f4af6541136
-- statement:
--   Prove that $1+\frac{1}{4}+\frac{1}{9}+...+\frac{1}{n^2} <\frac{7}{4}$ for any $n \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41432 : ∀ n : ℕ, (∑ i in Finset.range n, (1 / (i + 1)^2)) < 7 / 4   :=  by sorry
