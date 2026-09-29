-- Prove2me | Theorems.Thm_lean_workbook_plus_62355
-- name    : lean_workbook_plus_62355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5a442b09-23b6-4e0e-a3b5-6a8344eb4f04
-- statement:
--   let's take $X=$ { $A_i $ satisfying the conditions} and $Y=$ { $A_i^C$ such that $A_i\in X$ }\nNOTE: $A_i^C=S$ \ $A_i$ is the complement of $A_i$ in $S$\n\nobviously $\left |X\bigcap Y \right |= 0$ and $|X|=|Y|=m$\n\nso $2m=|X|+|Y|< 2^n:$ the number of elements of $S$ \nthen $m\le 2^{n-1}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62355  (m n : ℕ)
  (h₀ : 0 < m ∧ 0 < n)
  (h₁ : 2 * m < 2^n) :
  m ≤ 2^(n - 1) - 1   :=  by sorry
