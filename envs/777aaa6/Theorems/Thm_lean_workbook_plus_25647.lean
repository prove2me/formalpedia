-- Prove2me | Theorems.Thm_lean_workbook_plus_25647
-- name    : lean_workbook_plus_25647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f35cf6de-2f4f-41d3-ad09-565035d3fb95
-- statement:
--   Prove that, for each real number x, we have ${ [x] - 2[\frac{x}{2}] <= 1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25647 (x : ℝ) : (⌊x⌋ - 2 * ⌊x/2⌋) ≤ 1   :=  by sorry
