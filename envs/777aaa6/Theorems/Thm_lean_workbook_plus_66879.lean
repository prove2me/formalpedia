-- Prove2me | Theorems.Thm_lean_workbook_plus_66879
-- name    : lean_workbook_plus_66879
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/4e40713c-f631-42b1-a200-2020e6c85ddd
-- statement:
--   Prove that for $ 2/3 < x < 1 $, $\max \left \lbrace \frac{1-x}{1+3x}, \frac{3x^2-x-1}{3x} \right \rbrace < \frac{1}{3} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66879 (x : ℝ) (hx1 : 2/3 < x) (hx2 : x < 1) : max ((1 - x) / (1 + 3 * x)) (3 * x ^ 2 - x - 1) / (3 * x) < 1 / 3   :=  by sorry
