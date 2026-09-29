-- Prove2me | Theorems.Thm_lean_workbook_plus_13539
-- name    : lean_workbook_plus_13539
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/55540e1a-8a88-49cd-b396-05b5c434e479
-- statement:
--   Prove: $\binom{2n+1}{0}+\binom{2n+1}{1}+\binom{2n+1}{2}+...+\binom{2n+1}{n}=4^{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13539 : ∀ n : ℕ, ∑ k in Finset.range (n+1), choose (2*n+1) k = 4^n   :=  by sorry
