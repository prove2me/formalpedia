-- Prove2me | Theorems.Thm_lean_workbook_plus_72264
-- name    : lean_workbook_plus_72264
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/4377b8ee-e328-43fd-aa18-3719516905f9
-- statement:
--   Assume that there are finitely many $n$ satisfying $f(n) = n$ . This implies that there exists some $N \in \mathbb{N}$ such that for all $n \geq N$ , $f(n) \neq n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72264 (f : ℕ → ℕ) (hf : Set.Finite {n | f n = n}) : ∃ N, ∀ n ≥ N, f n ≠ n   :=  by sorry
