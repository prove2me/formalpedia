-- Prove2me | Theorems.Thm_lean_workbook_plus_67031
-- name    : lean_workbook_plus_67031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/c0bb7e17-49ab-49f3-b436-864a469e55e4
-- statement:
--   Prove that for all $n \in \mathbb{N}$, $a_n \in \mathbb{N}$, where $a_1=a_2=1$ and $a_n=\frac{a_{n-1}^2+2}{a_{n-2}}$ for $n>2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67031 (n : ℕ) (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 1) (a_rec : ∀ n, n > 2 → a n = (a (n-1)^2 + 2) / a (n-2)) : ∀ n, a n ∈ Set.range a   :=  by sorry
