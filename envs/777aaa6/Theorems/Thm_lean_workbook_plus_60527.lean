-- Prove2me | Theorems.Thm_lean_workbook_plus_60527
-- name    : lean_workbook_plus_60527
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f0d3787c-8945-447f-91d9-7a62705ba9c5
-- statement:
--   Prove that $\frac{1}{2}\cdot \frac{3}{4}\cdot \frac{5}{6}\cdot ...\cdot \frac{2n-1}{2n}<\frac{1}{\sqrt{3n}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60527 : ∀ n : ℕ, (∏ i in Finset.range n, (2 * i - 1) / (2 * i)) < 1 / (Real.sqrt (3 * n))   :=  by sorry
