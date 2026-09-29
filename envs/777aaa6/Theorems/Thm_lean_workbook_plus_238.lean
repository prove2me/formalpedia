-- Prove2me | Theorems.Thm_lean_workbook_plus_238
-- name    : lean_workbook_plus_238
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/3fcc9073-d33d-4035-b626-37cbdba347a9
-- statement:
--   Prove that for all positive reals $x_1, x_2$, the following inequality holds:\n\n $x_1 + x_2 \geq 2\sqrt{x_1x_2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_238 (x_1 x_2 : ℝ) (hx_1 : 0 < x_1) (hx_2 : 0 < x_2) : x_1 + x_2 ≥ 2 * Real.sqrt (x_1 * x_2)   :=  by sorry
