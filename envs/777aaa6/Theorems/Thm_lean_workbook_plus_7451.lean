-- Prove2me | Theorems.Thm_lean_workbook_plus_7451
-- name    : lean_workbook_plus_7451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/68589e7d-b99b-42f4-960a-d3f9d17d96cf
-- statement:
--   Therefore, we have $x+\sqrt{x^2+1}-(x-\sqrt{x^2+1})=2\sqrt{x^2+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7451  (x : ℝ) :
  x + Real.sqrt (x^2 + 1) - (x - Real.sqrt (x^2 + 1)) = 2 * Real.sqrt (x^2 + 1)   :=  by sorry
