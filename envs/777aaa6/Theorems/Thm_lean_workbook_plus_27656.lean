-- Prove2me | Theorems.Thm_lean_workbook_plus_27656
-- name    : lean_workbook_plus_27656
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/84738fe2-5d3b-41e4-afc7-e150c71e330a
-- statement:
--   By Cauchy's Inequality: $\sqrt{(a^2+b^2+c^2 + 2ab)(4+1)}\geq(2a+2b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27656 (a b c : ℝ) : (a^2 + b^2 + c^2 + 2 * a * b) * (4 + 1) ≥ (2 * a + 2 * b + c)^2   :=  by sorry
