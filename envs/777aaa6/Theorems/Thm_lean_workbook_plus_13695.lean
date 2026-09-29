-- Prove2me | Theorems.Thm_lean_workbook_plus_13695
-- name    : lean_workbook_plus_13695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/dc74cf4f-0aac-49e2-b08f-927732b2c4d9
-- statement:
--   $ x+y=7$ \n $ x^2-y^2=21$ \n $ y=7-x$ \n $ x^2-(7-x)^2$ \n $ x^2-x^2+14x-49$ \n $ 14x=70$ \n $ x=5$ \n $ \implies\ y=2$ \n $ 2x+3y=2*5+3*2=10+6=16$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13695  (x y : ℝ)
  (h₀ : x + y = 7)
  (h₁ : x^2 - y^2 = 21)
  (h₂ : y = 7 - x)
  (h₃ : x^2 - (7 - x)^2 = 21) :
  2 * x + 3 * y = 16   :=  by sorry
