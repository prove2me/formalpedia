-- Prove2me | Theorems.Thm_lean_workbook_plus_26199
-- name    : lean_workbook_plus_26199
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/531224ce-4ee5-4ac5-8869-0d85bcb1f88f
-- statement:
--   ($(\\sqrt2-t))(\\frac{5}{\\sqrt2}-t)\\geq0,$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26199 : ∀ t : ℝ, (Real.sqrt 2 - t) * (5 / Real.sqrt 2 - t) ≥ 0   :=  by sorry
