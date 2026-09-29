-- Prove2me | Theorems.Thm_lean_workbook_plus_73553
-- name    : lean_workbook_plus_73553
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/91de035f-5fc1-4099-8fae-4020a8f92600
-- statement:
--   Prove that for positive x, $x + \frac{1}{x} \geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73553 (x : ℝ) (hx : 0 < x) : x + 1 / x ≥ 2   :=  by sorry
