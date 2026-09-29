-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_66265
-- name    : WorkbookCorrected.plus_66265
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:50:55.653719+00:00
-- url     : https://prove2.me/theorems/876f86f0-2fc2-49fe-9545-4afa04cfb482
-- title:
--   Determining a sequence from a symmetric index relation
-- statement:
--   The sequence $\{a_n\}_{n\geq 0}$ of real numbers satisfies the relation: $ a_{m+n} + a_{m-n} - m + n -1 = \frac12 (a_{2m} + a_{2n}) $ for all non-negative integers $m$ and $n$ , $m \ge n$ . If $a_1 = 3$ find $a_{2004}$ .
--
--   The required value is a₂₀₀₄=4018021.
--
--   Formalization Note: The source condition m≥n is an antecedent restricting when the recurrence applies. The original formalization asserted m≥n for every pair of natural numbers, making its assumptions inconsistent. This correction restores the implication and proves the requested value from the original recurrence and initial value.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_66265 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_66265; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_66265 (a : ℕ → ℝ) (h0 : a 1 = 3)
    (h : ∀ m n : ℕ, n ≤ m → a (m+n)+a (m-n)-(m:ℝ)+(n:ℝ)-1 = 1/2*(a (2*m)+a (2*n))) : a 2004 = 4018021 := by sorry
