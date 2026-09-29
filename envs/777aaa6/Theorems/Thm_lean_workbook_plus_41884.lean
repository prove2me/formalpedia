-- Prove2me | Theorems.Thm_lean_workbook_plus_41884
-- name    : lean_workbook_plus_41884
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/41346fe8-d491-42a7-94b6-f2cfe8acdd76
-- statement:
--   Prove that: $ \sum_{k = 1}^n (a_k - 1)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41884 (n : ℕ) (a : ℕ → ℕ) : 0 ≤ ∑ k in Finset.range n, (a k - 1) ^ 2   :=  by sorry
