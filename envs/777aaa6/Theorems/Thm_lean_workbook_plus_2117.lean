-- Prove2me | Theorems.Thm_lean_workbook_plus_2117
-- name    : lean_workbook_plus_2117
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ffda6bd4-054d-4237-b654-448933bf6789
-- statement:
--   Adding these two yields $2|z|^4\le 2|z|^2 \implies |z|^2\le 1$ since it is also true for $z=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2117  (z : ℂ) :
  2 * Complex.abs z^4 ≤ 2 * Complex.abs z^2 → Complex.abs z^2 ≤ 1   :=  by sorry
