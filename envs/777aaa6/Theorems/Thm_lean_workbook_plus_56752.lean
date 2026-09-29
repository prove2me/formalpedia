-- Prove2me | Theorems.Thm_lean_workbook_plus_56752
-- name    : lean_workbook_plus_56752
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/23439555-e737-43d0-b6b3-e13c56bc6065
-- statement:
--   We know that $3x+5y=29$ and $41x+23y=215$. What is $x^2+y^2$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56752 (x y : ℝ) (h₁ : 3*x + 5*y = 29) (h₂ : 41*x + 23*y = 215) : x^2 + y^2 = 25   :=  by sorry
