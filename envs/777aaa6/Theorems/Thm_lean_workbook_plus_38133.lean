-- Prove2me | Theorems.Thm_lean_workbook_plus_38133
-- name    : lean_workbook_plus_38133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b711b227-13cc-40fc-bc73-7e41b331e49f
-- statement:
--   Find all functions $f(x)$ from the set $S = \{ 1, 2, 3, 4, 5 \}$ to itself such that $f(f(x)) = x$ for all $x \in S$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38133 (S : Finset ℕ) (hS : S = {1, 2, 3, 4, 5}) : ∃ f : ℕ → ℕ, ∀ x ∈ S, f (f x) = x   :=  by sorry
