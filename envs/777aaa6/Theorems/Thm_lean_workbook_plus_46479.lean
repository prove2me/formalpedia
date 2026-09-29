-- Prove2me | Theorems.Thm_lean_workbook_plus_46479
-- name    : lean_workbook_plus_46479
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9555f043-52d7-446d-ba46-da37e543010e
-- statement:
--   Find the first four terms of the Laurent series of $\frac{1}{e^z-1}$ about 0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46479 (h : ∀ z : ℂ, 0 < z.re) : (1 / (exp z - 1)) = 1 / z - 1 / 2 + z / 12 + 0 * z ^ 2   :=  by sorry
