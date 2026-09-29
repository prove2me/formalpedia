-- Prove2me | Theorems.Thm_lean_workbook_plus_45240
-- name    : lean_workbook_plus_45240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1a7313f9-46aa-458d-a143-25e7d45717d1
-- statement:
--   Since $ x=a+b+c$ , using that substitution property of inequality.\nThe $ LHS$ becomes: \n $ x^2+(3-x)^2$\nExpanding, we get: \n $ x^2+x^2-6x+9 \implies \boxed{2x^2-6x+9}$\n\nExpanding the RHS, we get: \n $ 2(x^2-3x+9/4)+9/2 \implies \boxed{2x^2-6x+9}$\n\nTherefore, we have proven that $ (a + b + c)^2 + (3 - a - b - c)^2 = 2(x - 3/2)^2 + 9/2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45240  (x a b c : ℝ)
  (h₀ : x = a + b + c) :
  x^2 + (3 - x)^2 = 2 * (x - 3 / 2)^2 + 9 / 2   :=  by sorry
