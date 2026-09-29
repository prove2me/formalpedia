-- Prove2me | Theorems.Thm_lean_workbook_plus_1896
-- name    : lean_workbook_plus_1896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8bea3cba-abbe-4a52-b04e-f96d46bac7cd
-- statement:
--   Find all functions $f: \mathbb{N} \rightarrow \mathbb{N}$ such that $f(m + n) = f(m) + f(n) + mn$ for all positive integers $m$ and $n$, and $f(1) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1896 (f : ℕ → ℕ) (hf: f 1 = 1) (hf1: ∀ m n: ℕ, f (m + n) = f m + f n + m * n): ∀ n:ℕ, f n = n * (n + 1) / 2   :=  by sorry
