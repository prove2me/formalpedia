-- Prove2me | Theorems.Thm_lean_workbook_plus_41634
-- name    : lean_workbook_plus_41634
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8bd394bc-af0e-442b-a12d-84fe12481cae
-- statement:
--   Prove that $\sum_{n=0}^{m}\dbinom{n+4}{n} =\dbinom{m+5}{m}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41634 (m : ℕ) : ∑ n in Finset.range (m+1), choose (n+4) n = choose (m+5) m   :=  by sorry
