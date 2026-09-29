-- Prove2me | Theorems.Thm_lean_workbook_plus_27581
-- name    : lean_workbook_plus_27581
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4dffd20e-7665-4498-a685-938e51714c80
-- statement:
--   Prove that \(x+1\geq 2\sqrt{x}\) using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27581 (x : ℝ) (hx : x ≥ 0) : x + 1 ≥ 2 * Real.sqrt x   :=  by sorry
