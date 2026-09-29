-- Prove2me | Theorems.Thm_lean_workbook_plus_40693
-- name    : lean_workbook_plus_40693
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a8972290-af2b-41ff-9a93-98cc96813462
-- statement:
--   $\frac{1}{1^{1}}+\frac{1}{2^{2}}+...+\frac{1}{n^{2}}>\sqrt[n+1]{\frac{n+1}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40693 (n : ℕ) : ∀ n : ℕ, (∑ i in Finset.range n, (1/(i + 1)^2)) > ((n + 1) / 2) ^ (1 / (n + 1))   :=  by sorry
