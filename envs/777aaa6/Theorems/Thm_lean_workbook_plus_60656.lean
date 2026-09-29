-- Prove2me | Theorems.Thm_lean_workbook_plus_60656
-- name    : lean_workbook_plus_60656
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c758cbe5-720d-469d-ae8a-22f29a8eb5b5
-- statement:
--   The equation is $ .85p-90=.75p-15\\Rightarrow .1p=75$ , so $ p=750$ . Answer is $ A$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60656  (p : ℝ)
  (h₀ : 0.85 * p - 90 = 0.75 * p - 15) :
  p = 750   :=  by sorry
