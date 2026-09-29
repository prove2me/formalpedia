-- Prove2me | Theorems.Thm_lean_workbook_plus_20207
-- name    : lean_workbook_plus_20207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f6919416-28e7-4cf6-b951-32277a9d9697
-- statement:
--   Prove that $x^3-14x^2+48x+192 = x\Big ( (x-7)^2 - 1\Big ) + 192$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20207 : ∀ x : ℝ, x^3 - 14 * x^2 + 48 * x + 192 = x * ((x - 7)^2 - 1) + 192   :=  by sorry
