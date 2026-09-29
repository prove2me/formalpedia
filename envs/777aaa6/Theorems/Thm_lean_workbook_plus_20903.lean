-- Prove2me | Theorems.Thm_lean_workbook_plus_20903
-- name    : lean_workbook_plus_20903
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6fdf0c76-412a-4504-babe-1cc05be6f6f6
-- statement:
--   Prove that, for all $n \in \mathbb{N}$ \n\begin{align*} \frac{1}{1}+\frac{1}{3}+\frac{1}{5}+\ldots+\frac{1}{2n+1} \not\in \mathbb{Z} \end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20903 (n : ℕ) :
    ∑ k in Finset.range (n+1), (1 : ℚ) / (2 * k + 1) ≠ ∑ k in Finset.range (n+1), (1 : ℤ) / (2 * k + 1)   :=  by sorry
