-- Prove2me | Theorems.Thm_lean_workbook_plus_37288
-- name    : lean_workbook_plus_37288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d3f4e288-cb55-4a12-b10d-f13f47a31136
-- statement:
--   Show that the expression $ x^3-5x^2+8x-4 $ is nonegative, for every $ x\in [1,\infty ) . $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37288 (x : ℝ) (hx: 1 ≤ x) : x^3 - 5 * x^2 + 8 * x - 4 ≥ 0   :=  by sorry
