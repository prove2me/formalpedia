-- Prove2me | Theorems.Thm_lean_workbook_plus_78654
-- name    : lean_workbook_plus_78654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e1370d8e-f8d6-42df-9409-7308b46138c6
-- statement:
--   Find $y$ when $x=200$ using the linear function $y = \frac{5}{12} \cdot x - \frac{5 \cdot 110}{12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78654 (x y : ℝ) (h₁ : x = 200) (h₂ : y = 5/12 * x - 5*110/12) : y = 37.5   :=  by sorry
