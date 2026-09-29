-- Prove2me | Theorems.Thm_lean_workbook_plus_59963
-- name    : lean_workbook_plus_59963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/da7f75ba-916b-4185-8d09-46fc111033b1
-- statement:
--   Solve this system of equations with $ x,y \in R$ : \n\n$ \left\{\begin {array} {c}{x^3 + y^2 = 2 \ x^2 + xy + y^2 - y = 0 \end {array}}$ \n\nPlease post the full of your solution. Thank you very much.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59963 (x y : ℝ) (h₁ : x^3 + y^2 = 2) (h₂ : x^2 + x*y + y^2 - y = 0) : x = 1 ∧ y = 1   :=  by sorry
