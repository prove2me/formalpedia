-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_10014
-- name    : WorkbookCorrected.plus_10014
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:10:42.311489+00:00
-- url     : https://prove2.me/theorems/b39c1577-26d3-48e3-a62e-3ff9d54a1dbd
-- title:
--   A harmonic lower bound for an implicit quadratic recurrence
-- statement:
--   Let $a_1, a_2, a_3, . . .$ be a sequence of positive real numbers that satisfies $a_1 = 1$ and $a^2_{n+1} + a_{n+1} = a_n$ for every natural number $n$ . Prove that $a_n \ge \frac{1}{n}$ for every natural number $n$ .
--
--   Formalization Note: The original formalization omitted the source positivity assumption and quantified the recurrence and conclusion at index0. This correction restores positivity and the source indexing n≥1.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_10014 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10014; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_10014 (a : ℕ → ℝ) (h0 : a 1=1) (hp : ∀ n : ℕ, 1≤n → 0<a n)
    (h : ∀ n : ℕ, 1≤n → (a (n+1))^2+a (n+1)=a n) :
    ∀ n : ℕ, 1≤n → a n ≥ 1/(n:ℝ) := by sorry
