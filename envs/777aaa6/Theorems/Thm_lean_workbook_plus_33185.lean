-- Prove2me | Theorems.Thm_lean_workbook_plus_33185
-- name    : lean_workbook_plus_33185
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/bfe9802f-4b97-4b48-9fe3-61fb085f8eb0
-- statement:
--   Prove that $ \sum_{n = 0}^{\infty}{\frac {1}{n!}} = e$ using the Maclaurin expansion of $ e^{x}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33185 : ∑' n : ℕ, (1 / n! : ℝ) = exp 1   :=  by sorry
