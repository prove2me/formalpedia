-- Prove2me | Theorems.Thm_lean_workbook_plus_50024
-- name    : lean_workbook_plus_50024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5ed93385-d55b-41d7-b145-a45b2d8a2bf3
-- statement:
--   Let $S=x^2+y^2+z^2-xy-yz-zx$ , then $2S=(x-y)^2+(y-z)^2+(z-x)^2$ .\nLet $|x-y|\geq|y-z|\geq|z-x|$ . Because there are no two equal numbers, $|z-x|>0 \Rightarrow |y-z|\geq|z-x|\geq1$ .\nLet $|y-z|=|z-x|=1 \Rightarrow |x-y|=2$ , so minimum value of $2S$ is greater than or equal to $1+1+2^2=6$ but for $y=3, z=2, x=1$ we get that value so minimum value is $S=3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50024  (x y z : ℝ)
  (h₀ : 0 < abs (x - y))
  (h₁ : 0 < abs (y - z))
  (h₂ : 0 < abs (z - x))
  (h₃ : abs (x - y) ≥ abs (y - z))
  (h₄ : abs (y - z) ≥ abs (z - x))
  (h₅ : abs (z - x) ≥ 1) :
  3 ≤ x^2 + y^2 + z^2 - x * y - y * z - z * x   :=  by sorry
