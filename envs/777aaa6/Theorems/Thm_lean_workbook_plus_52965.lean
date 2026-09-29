-- Prove2me | Theorems.Thm_lean_workbook_plus_52965
-- name    : lean_workbook_plus_52965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/bc8b247f-cc25-4be1-b5f3-6ba8f908cf6b
-- statement:
--   Let $S=\{1, 2,3, \cdots, 12\}$ . How many functions $f: S \rightarrow S$ are there such that $f(f(x))=x$ and $f(x)-x$ is divisible by 3 ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52965 (S : Finset ℕ) (hS : S = Finset.Icc 1 12) : ∃ f : ℕ → ℕ, ∀ x ∈ S, f (f x) = x ∧ (f x - x) % 3 = 0   :=  by sorry
