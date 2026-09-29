-- Prove2me | Theorems.Thm_lean_workbook_plus_49595
-- name    : lean_workbook_plus_49595
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fcfd9ef2-45c8-4089-a550-733220bed17b
-- statement:
--   A sequence of numbers $a_1,a_2,a_3,\cdots$ satisfies $a_1=\frac{1}{2}$ and $a_1+a_2+\cdots+a_n=n^2a_n$ for $n\geq 1$ . Find $a_n$ in terms of $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49595 {a : ℕ → ℝ} (a1 : a 0 = 1 / 2) (a2 : ∀ n, (∑ i in Finset.range (n + 1), a i) = n^2 * a n) : a n = 1 / (n * (n + 1))   :=  by sorry
