-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_13202
-- name    : WorkbookCorrected.plus_13202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:18:20.781414+00:00
-- url     : https://prove2.me/theorems/630f33da-ab09-4e4a-aa2c-ea85395fd096
-- title:
--   A strict rational lower bound for a quadratic recurrence
-- statement:
--   Prove that for the sequence $\{x_n\}$ defined by $x_1=\frac 12, \ x_{n+1}=x_n+\left(\frac{x_n}n\right)^2$, we have $x_n>\frac{6n}{5n+6}, \forall n\geq 3$.
--
--   Formalization Note: The recurrence is restricted to positive indices, as in the source sequence starting at1. The complete lower bound is proved for every n≥3.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_13202 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_13202; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_13202 (x : ℕ → ℝ) (hx : x 1=1/2)
    (h : ∀ n : ℕ, 1≤n → x (n+1)=x n+(x n/(n:ℝ))^2) :
    ∀ n : ℕ, 3≤n → x n > 6*(n:ℝ)/(5*(n:ℝ)+6) := by sorry
