-- Prove2me | Theorems.Thm_lean_workbook_plus_57419
-- name    : lean_workbook_plus_57419
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8cc275fa-e87e-46ed-ad39-5e91cde9c7fa
-- statement:
--   Prove that $1+2+3+...+n=\frac{n(n+1)}{2}$ by considering the arithmetic progression and the formula for the sum of $n$ terms
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57419 : ∀ n, (∑ i in Finset.range (n + 1), i) = n * (n + 1) / 2   :=  by sorry
