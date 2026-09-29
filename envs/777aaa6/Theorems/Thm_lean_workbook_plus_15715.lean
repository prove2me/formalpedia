-- Prove2me | Theorems.Thm_lean_workbook_plus_15715
-- name    : lean_workbook_plus_15715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5849c24b-7aef-432c-8159-64553a5bc8d6
-- statement:
--   case 1: $ x=5$ \n $ y+\sqrt{25-y^2}=7$ \n $ 25-y^2=(7-y)^2$ \n $ 2y^2-14y+24=0$ \n $ y=4 ,y=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15715  (x y : ℝ)
  (h₀ : x = 5)
  (h₁ : y + Real.sqrt (25 - y^2) = 7)
  (h₂ : 25 - y^2 = (7 - y)^2) :
  2 * y^2 - 14 * y + 24 = 0   :=  by sorry
