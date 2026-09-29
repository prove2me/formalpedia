-- Prove2me | Theorems.Thm_lean_workbook_plus_64634
-- name    : lean_workbook_plus_64634
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1eb761ce-0361-427d-8c2d-f44e32224683
-- statement:
--   Prove that $n+(n-1)+(n-2)+\cdots+2+1 = \frac{n(n+1)}{2}$ for all integers $n\ge2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64634 (n : ℕ) (h : n ≥ 2) : ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2   :=  by sorry
