-- Prove2me | Theorems.Thm_lean_workbook_plus_526
-- name    : lean_workbook_plus_526
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b7c2e3b6-0593-47cd-a48f-31f9cbda7d31
-- statement:
--   Prove that $1 \times 2 \times 3 \times \ldots \times n \geq 2^{n-1}$ for $n$ in the set of counting numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_526 : ∀ n : ℕ, n! ≥ 2 ^ (n - 1)   :=  by sorry
