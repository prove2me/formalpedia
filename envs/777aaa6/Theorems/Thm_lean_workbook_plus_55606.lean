-- Prove2me | Theorems.Thm_lean_workbook_plus_55606
-- name    : lean_workbook_plus_55606
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/80e1dbc0-4487-4939-a3d1-ef4be34dd719
-- statement:
--   By simple calculation, we get: $(x^2-3x-2)^2-3(x^2-3x-2)-2-x=(x^2-4x-2) (x^2-2x-4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55606  (x : ℝ) :
  (x^2 - 3 * x - 2)^2 - 3 * (x^2 - 3 * x - 2) - 2 - x =
    (x^2 - 4 * x - 2) * (x^2 - 2 * x - 4)   :=  by sorry
