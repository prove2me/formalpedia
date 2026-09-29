-- Prove2me | Theorems.Thm_lean_workbook_plus_69558
-- name    : lean_workbook_plus_69558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/fad35768-9598-4162-8678-33aa807088fd
-- statement:
--   SolutionLet $w, x, y,$ and $z$ be the four numbers. Then, \n\n \begin{align*} w + x &= 42 \ x + y &= 52 \ y + z &= 60. \end{align*} Adding up the three equations we get that $w + 2x + 2y + z = w + z + 2(x+y) = w + z + 2(52) = 154$ . Thus $w + z = 50.$ Thus, the average of the first and last numbers is $\frac{w + z}{2} = \boxed{25}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69558  (w x y z : ℝ)
  (h₀ : w + x = 42)
  (h₁ : x + y = 52)
  (h₂ : y + z = 60) :
  (w + z) / 2 = 25   :=  by sorry
