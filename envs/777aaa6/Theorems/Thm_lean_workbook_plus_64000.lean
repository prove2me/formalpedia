-- Prove2me | Theorems.Thm_lean_workbook_plus_64000
-- name    : lean_workbook_plus_64000
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/627bf0de-9ef3-4ed9-a297-8ad4d04a422c
-- statement:
--   With $x = 2$ we want to find all $y$ for which one has $2^y - 2 = y^2 - y$ or equivalently $2^y = y^2 + (2-y).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64000 (x y : ℝ) (hx : x = 2) : x^y - x = y^2 - y ↔ 2^y - 2 = y^2 - y   :=  by sorry
