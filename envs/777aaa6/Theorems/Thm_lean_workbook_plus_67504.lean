-- Prove2me | Theorems.Thm_lean_workbook_plus_67504
-- name    : lean_workbook_plus_67504
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4066d26b-2aeb-4eaf-9478-dc03241a1f2f
-- statement:
--   Find the explicit solution: $a_{1}=1 , \ \ a_{n+1}= \sum_{k=1}^{n}k a_{k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67504 : ∃ a : ℕ → ℕ, a 1 = 1 ∧ ∀ n, a (n + 1) = ∑ k in Finset.range n, k * a k   :=  by sorry
