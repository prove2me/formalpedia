-- Prove2me | Theorems.Thm_lean_workbook_plus_16142
-- name    : lean_workbook_plus_16142
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/de8ea728-4bfd-4478-b864-2063796107e0
-- statement:
--   Find the number of functions $f: \{1, 2, 3, 4, 5\} \rightarrow \{1, 2, 3, 4, 5\}$ such that $f(f(i)) \neq i$ for all $i$ in $\{1, 2, 3, 4, 5\}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16142 {f : ℕ → ℕ | ∀ i ∈ ({1, 2, 3, 4, 5} : Finset ℕ), f (f i) ≠ i} = {f : ℕ → ℕ | ∀ i ∈ ({1, 2, 3, 4, 5} : Finset ℕ), f (f i) ≠ i}   :=  by sorry
