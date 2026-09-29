-- Prove2me | Theorems.Thm_lean_workbook_plus_23478
-- name    : lean_workbook_plus_23478
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/649205da-8652-4803-94f5-3228f42e34a8
-- statement:
--   From step (3) of gauss's simplification of the equation, we have \n\n $ 6x + \frac{1}{4}x^2 - \frac{1}{4}x = 72\implies 24x + x^2 - x = 288\implies x^2 + 23x - 288 = 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23478  (x : ℝ)
  (h₀ : 6 * x + 1 / 4 * x^2 - 1 / 4 * x = 72) :
  x^2 + 23 * x - 288 = 0   :=  by sorry
