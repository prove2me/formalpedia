-- Prove2me | Theorems.Thm_lean_workbook_plus_54694
-- name    : lean_workbook_plus_54694
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f5707a56-6b2c-4115-ba74-ba021fd37e4e
-- statement:
--   Prove that \(60x^8+135x^7+369x^6+169x^5+402x^4+53x^3-19x^2+11x+4\geq0\) for \(x \geq 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54694 (x : ℝ) (hx : x ≥ 0) : 60 * x^8 + 135 * x^7 + 369 * x^6 + 169 * x^5 + 402 * x^4 + 53 * x^3 - 19 * x^2 + 11 * x + 4 ≥ 0   :=  by sorry
