-- Prove2me | Theorems.Thm_WorkbookCorrected_base_56341
-- name    : WorkbookCorrected.base_56341
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:05:38.684094+00:00
-- url     : https://prove2.me/theorems/24a03de2-2591-4262-8705-5ac2c130d16e
-- title:
--   Boundedness of a quadratic recurrence below its critical initial value
-- statement:
--   Let $0<x_1<1$ and, for every integer $n\ge1$, define
--   \[x_{n+1}=x_n+\frac{x_n^2}{n^2}.\]
--   Then there exists a real number $M$ such that $x_n<M$ for every $n\ge1$.
--
--   Formalization Note: The original source formalization incorrectly assumed that every term was already between zero and one. This correction uses only the source initial condition and recurrence and proves boundedness. The sequence is indexed from1 as in the source.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_56341 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56341; Apache-2.0

import Mathlib

theorem WorkbookCorrected.base_56341 : ∀ (x : ℕ → ℝ) (h0 : 0 < x 1) (h1 : x 1 < 1)
    (hrec : ∀ n : ℕ, 1 ≤ n → x (n+1) = x n + (x n)^2/(n:ℝ)^2),
    ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n → x n < M := by sorry
