-- Prove2me | Theorems.Thm_lean_workbook_plus_3547
-- name    : lean_workbook_plus_3547
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/7e82cd2e-64f2-432c-9809-18c67fcb2e73
-- statement:
--   Given that $a_n=b_n^2$ and $b_n=1$ for all $n$, find $a_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3547 (a : ℕ → ℕ) (b : ℕ → ℕ) (h₁ : ∀ n, a n = (b n)^2) (h₂ : ∀ n, b n = 1) : a n = 1   :=  by sorry
