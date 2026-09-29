-- Prove2me | Theorems.Thm_lean_workbook_plus_43044
-- name    : lean_workbook_plus_43044
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/14d3afe9-708d-4b7f-99ba-7b426124fb38
-- statement:
--   prove that $(x - 3)(x^3 + 3x^2 + 9x - 27) \ge 0$ for $x \ge 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43044 (x : ℝ) (hx : x ≥ 3) : (x - 3) * (x^3 + 3 * x^2 + 9 * x - 27) ≥ 0   :=  by sorry
