-- Prove2me | Theorems.Thm_lean_workbook_plus_67063
-- name    : lean_workbook_plus_67063
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/bb2dbc6a-25cc-4934-a64c-0b73746ad708
-- statement:
--   Find the sum of the reciprocals of the first 5 distinct terms in the infinite sequence of the form $a_k = \frac{k}{19} + \frac{k}{17}$, where $k = 1, 2, 3, 4, 5$. Express your answer as a fraction in simplest form.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67063 (a : ℕ → ℚ) (h : ∀ k : ℕ, a k = k / 19 + k / 17) : ∑ i in Finset.range 5, (1 / a i) = 159 / 323   :=  by sorry
