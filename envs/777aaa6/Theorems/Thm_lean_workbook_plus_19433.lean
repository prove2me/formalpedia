-- Prove2me | Theorems.Thm_lean_workbook_plus_19433
-- name    : lean_workbook_plus_19433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5d44151c-1b32-4784-b93f-4e89b53a24e6
-- statement:
--   Express $a_n$ in terms of $b_n$ where $a_n = 2b_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19433 (a b : ℕ → ℕ) (h₁ : ∀ n, a n = 2 * b n) : a = fun n ↦ 2 * b n   :=  by sorry
