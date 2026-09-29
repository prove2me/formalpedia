-- Prove2me | Theorems.Thm_lean_workbook_plus_82440
-- name    : lean_workbook_plus_82440
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e9e3e211-c26c-4ed2-892f-bfb4e4837be4
-- statement:
--   Factor $x^5-15 x^4+85 x^3-225 x^2+274 x-120$ over the reals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82440 : ∀ x : ℝ, x^5 - 15 * x^4 + 85 * x^3 - 225 * x^2 + 274 * x - 120 = (x-1)*(x-2)*(x-3)*(x-4)*(x-5)   :=  by sorry
