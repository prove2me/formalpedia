-- Prove2me | Theorems.Thm_lean_workbook_plus_74095
-- name    : lean_workbook_plus_74095
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/423d2167-b7c3-4de8-8b37-2f6ef07a4148
-- statement:
--   Prove that $4\sum (a-\frac12)^{2}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74095 (n : ℕ) (a : ℕ → ℝ) : 4 * ∑ i in Finset.range n, (a i - 1 / 2)^2 ≥ 0   :=  by sorry
