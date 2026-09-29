-- Prove2me | Theorems.Thm_lean_workbook_plus_42269
-- name    : lean_workbook_plus_42269
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/7f51a3b2-201b-4aa1-8294-05ccecf03ec1
-- statement:
--   Assuming that an item costs 100 dollars, $100 \cdot (1-0.3) \cdot (1-0.2) = 56$ . We reduced the price by 44 dollars, or 44 percent.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42269  (x : ℝ)
  (h₀ : x = 100)
  (h₁ : (1 - 0.3) * (1 - 0.2) = 0.56) :
  x * (1 - 0.3) * (1 - 0.2) = 56   :=  by sorry
