-- Prove2me | Theorems.Thm_lean_workbook_plus_71486
-- name    : lean_workbook_plus_71486
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/181b174d-bf26-40f0-a4d3-c04bb887c77e
-- statement:
--   A sequence of numbers $a_{1}, a_{2}, a_{3},...$ satisfies $a_{1}=\frac{1}{2}$ and $a_{1}+a_{2}+...+a_{n}=n^{2}a_{n}$ for $n\geqslant1$ . Find $a_{n}$ in terms of n.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71486 (n : ℕ) (a : ℕ → ℝ) (a1 : a 0 = 1 / 2) (a2 : ∀ n, (∑ i in Finset.range (n + 1), a i) = n^2 * a n) : a n = 1 / (n * (n + 1))   :=  by sorry
