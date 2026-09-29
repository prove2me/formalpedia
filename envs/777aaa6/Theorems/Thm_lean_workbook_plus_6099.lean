-- Prove2me | Theorems.Thm_lean_workbook_plus_6099
-- name    : lean_workbook_plus_6099
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a997735a-054e-4065-9b61-1611826cfedb
-- statement:
--   For $ P(x) = x^2$ , $ P(x + 1) - 1 = (x + 1)^2 - 1 = x^2 + 2x + 1 - 1 = x^2 + 2x = P(x) + P'(x)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6099  (x : ℤ) :
  (x + 1)^2 - 1 = x^2 + 2 * x   :=  by sorry
