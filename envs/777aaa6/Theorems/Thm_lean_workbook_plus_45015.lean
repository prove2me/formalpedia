-- Prove2me | Theorems.Thm_lean_workbook_plus_45015
-- name    : lean_workbook_plus_45015
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e4fac72f-7a72-4b4e-b17e-b239f35386f2
-- statement:
--   Prove that $x^2+2 \geq 2\sqrt{x^2+1}$ for all real values of $x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45015 (x : ℝ) : x^2 + 2 ≥ 2 * Real.sqrt (x^2 + 1)   :=  by sorry
