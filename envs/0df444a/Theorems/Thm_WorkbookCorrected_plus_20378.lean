-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_20378
-- name    : WorkbookCorrected.plus_20378
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:26:42.220245+00:00
-- url     : https://prove2.me/theorems/c5a5e752-46c5-40b5-b0d0-b76ec859bb40
-- title:
--   Divergence to positive infinity for a reciprocal-increment recurrence
-- statement:
--   Prove that $\lim_{n\to \infty} a_n = \infty$, where $(a_n)_{n\geq 1}$ is an increasing sequence defined by $a_1 = 1$ and $a_{n+1} = a_n + \frac{1}{a_n}$.
--
--   Formalization Note: The source initial value is at index1; the recurrence is used for n≥1. Divergence is stated by the full eventual-bound condition for every real threshold. Positivity and growth follow from the recurrence and initial value.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_20378 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20378; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_20378 (a : ℕ → ℝ) (h0 : a 1=1)
    (h : ∀ n : ℕ, 1≤n → a (n+1)=a n+1/a n) :
    ∀ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N≤n → M<a n := by sorry
