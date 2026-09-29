-- Prove2me | Theorems.Thm_lean_workbook_plus_71419
-- name    : lean_workbook_plus_71419
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c2fff8cd-168b-4292-b906-befc7597ed33
-- statement:
--   If $a \leq b + 1/n$ for all n ∈ N, then a ≤ b.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71419 (n : ℕ) (a b : ℝ) (hb : ∃ n, b < n) (hab : ∀ n, a ≤ b + 1/n) : a ≤ b   :=  by sorry
