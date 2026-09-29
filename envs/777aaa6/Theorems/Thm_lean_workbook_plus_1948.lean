-- Prove2me | Theorems.Thm_lean_workbook_plus_1948
-- name    : lean_workbook_plus_1948
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/670612b0-612d-469b-87c9-6fb9465b1fce
-- statement:
--   Prove that $(1+i\sqrt2)^2+(1-i\sqrt2)^2 = -2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1948 : (1 + (I * Real.sqrt 2))^2 + (1 - (I * Real.sqrt 2))^2 = -2   :=  by sorry
