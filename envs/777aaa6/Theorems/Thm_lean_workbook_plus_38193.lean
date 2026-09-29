-- Prove2me | Theorems.Thm_lean_workbook_plus_38193
-- name    : lean_workbook_plus_38193
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6cd209b6-f628-4322-b731-6466b2b04fdc
-- statement:
--   Find the general term $a_n$ and sum $S = a_1 + a_2 + \ldots + a_n$ for the sequence $a_1 = 2$, $a_{n+1} = 2a_n + 3$, $n \in \mathbb{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38193 (a : ℕ → ℕ) (a1 : a 0 = 2) (a_rec : ∀ n, a (n + 1) = 2 * a n + 3) : ∃ (f : ℕ → ℕ), ∀ n, a n = f n ∧ ∃ (f_sum : ℕ → ℕ), ∀ n, ∑ i in Finset.range (n + 1), a i = f_sum n   :=  by sorry
