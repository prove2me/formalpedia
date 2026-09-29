-- Prove2me | Theorems.Thm_lean_workbook_plus_59414
-- name    : lean_workbook_plus_59414
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/607c9c4a-3bbf-4667-b79f-bef4fd9578f7
-- statement:
--   Solve for $k$ in the equation $2k - 3 = \frac{1}{4}k^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59414 (k : ℝ) : 2 * k - 3 = 1 / 4 * k ^ 2 ↔ k = 2 ∨ k = 6   :=  by sorry
