-- Prove2me | Theorems.Thm_lean_workbook_plus_39014
-- name    : lean_workbook_plus_39014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f2a0afb2-1d7c-4c15-8344-dadd3ea2b7d8
-- statement:
--   Find all functions $f:\mathbb{N} \rightarrow \mathbb{N}$ such that: $f(1)=5$ , $f(f(n))=4n+9$ , $f(2^n)=2^{n+1}+3$ , $\forall n \in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39014 (f : ℕ → ℕ) (hf: f 1 = 5 ∧ ∀ n, f (f n) = 4*n + 9 ∧ f (2^n) = 2^(n+1) + 3) : ∃ f : ℕ → ℕ, f 1 = 5 ∧ ∀ n, f (f n) = 4*n + 9 ∧ f (2^n) = 2^(n+1) + 3   :=  by sorry
