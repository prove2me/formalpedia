-- Prove2me | Theorems.Thm_lean_workbook_plus_70713
-- name    : lean_workbook_plus_70713
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/aef56992-ee4f-4db7-a5e0-0925ac8d6c9f
-- statement:
--   x = gallons of 28% solution \nx+10 = gallons of 33% solution \ntotal gallons of acid = $\frac{28x+33(x+10)}{100}$ \ntotal gallons of overall solution = $2x+12$ \n\npercent acid of overall solution = \n\n$\frac{28x+33(x+10)}{100(2x+12)} = \frac{30}{100}\ 28x+330+33x=60x+360\ x=30\$ \n30 gal of 28% sol, 40 gal of 33% sol
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70713  (x : ℝ)
  (h₀ : x = gallons_of_28_percent_acid)
  (h₁ : x + 10 = gallons_of_33percent_acid)
  (h₂ : (28 * x + 33 * (x + 10)) / 100 = total_gallons_of_acid)
  (h₃ : 2 * x + 12 = total_gallons_of_overall_solutions)
  (h₄ : (28 * x + 33 * (x + 10)) / (100 * (2 * x + 12)) = 30 / 100) :
  x = 30   :=  by sorry
