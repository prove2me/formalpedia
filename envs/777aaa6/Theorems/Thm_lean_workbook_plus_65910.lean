-- Prove2me | Theorems.Thm_lean_workbook_plus_65910
-- name    : lean_workbook_plus_65910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/2b470b1a-f05d-40f5-8448-de8e474e997e
-- statement:
--   prove that $(a+b+c+d)^2 \geq 4(ab+bc+cd+da)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65910 (a b c d : ℝ) : (a + b + c + d) ^ 2 ≥ 4 * (a * b + b * c + c * d + d * a)   :=  by sorry
