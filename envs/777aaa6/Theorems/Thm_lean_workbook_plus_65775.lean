-- Prove2me | Theorems.Thm_lean_workbook_plus_65775
-- name    : lean_workbook_plus_65775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1d708015-2737-4747-a470-3239c540b824
-- statement:
--   Determine if the inequality $(x^2 + 1)^2(x^4 - x^3 + x^2 - x + 1)^2 > 0$ is true for all x > 0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65775 (x : ℝ) (hx : 0 < x) : (x^2 + 1)^2 * (x^4 - x^3 + x^2 - x + 1)^2 > 0   :=  by sorry
