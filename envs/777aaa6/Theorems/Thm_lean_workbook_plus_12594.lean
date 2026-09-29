-- Prove2me | Theorems.Thm_lean_workbook_plus_12594
-- name    : lean_workbook_plus_12594
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/27665e18-ac43-4e55-8dd6-9f3763fd5218
-- statement:
--   Prove that $1 + 2 + \ldots + n = \frac{n(n+1)}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12594 (n : ℕ) : ∑ i in (Finset.range (n+1)), i = n * (n+1) / 2   :=  by sorry
