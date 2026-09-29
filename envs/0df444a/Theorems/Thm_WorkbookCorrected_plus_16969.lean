-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_16969
-- name    : WorkbookCorrected.plus_16969
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:22:41.182812+00:00
-- url     : https://prove2.me/theorems/78663182-7044-44fd-9197-b5beef577971
-- title:
--   An invariant interval for a quartic rational recurrence
-- statement:
--   Define a sequence $\{x_n\}$ by $$x_1=2,x_{n+1}=\frac{x_n^4+9}{10x_n}.$$ Prove that $\frac45<x_n\leq\frac54$ for all $n>1$
--
--   Formalization Note: The recurrence is restricted to n≥1, matching the source initial index. The full interval bound is proved for every n≥2.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_16969 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_16969; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_16969 (x : ℕ → ℝ) (hx : x 1=2)
    (h : ∀ n : ℕ, 1≤n → x (n+1)=(x n^4+9)/(10*x n)) :
    ∀ n : ℕ, 2≤n → 4/5<x n ∧ x n≤5/4 := by sorry
