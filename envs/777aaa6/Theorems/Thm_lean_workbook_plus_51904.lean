-- Prove2me | Theorems.Thm_lean_workbook_plus_51904
-- name    : lean_workbook_plus_51904
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/57b3ba79-babf-470c-9fb5-05ebd1aa97c8
-- statement:
--   Prove that $\binom{n}{0}+\binom{n}{1}+\cdots+\binom{n}{n} = 2^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51904 : ∀ n, ∑ k in Finset.range (n+1), (Nat.choose n k) = 2^n   :=  by sorry
