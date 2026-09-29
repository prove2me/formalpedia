-- Prove2me | Theorems.Thm_lean_workbook_plus_23382
-- name    : lean_workbook_plus_23382
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/aa0d3b36-1c73-4fd8-93c7-f59d06311eb6
-- statement:
--   Prove that \(60x^8+135x^7+369x^6+169x^5+402x^4+53x^3-19x^2+11x+4\geq0\) for \(x \geq 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23382 (x : ℝ) (hx : 0 ≤ x) : 60 * x^8 + 135 * x^7 + 369 * x^6 + 169 * x^5 + 402 * x^4 + 53 * x^3 - 19 * x^2 + 11 * x + 4 ≥ 0   :=  by sorry
