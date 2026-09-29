-- Prove2me | Theorems.Thm_lean_workbook_plus_24593
-- name    : lean_workbook_plus_24593
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d3ade385-777a-4473-a79d-d44faf154180
-- statement:
--   If \\( \frac{x-1}{2} = \frac{y+1}{2} = \frac{z-2}{3}=t \\), then we have \\( x=2t+1,y=2t-1,z=3t+2 \\), so \\( xy+yz+zx=f(t)=16t^2+8t-1 \\), and this quadratic equation have minimum for \\( t=-\frac{1}{4} \\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24593  (x y z t : ℝ)
  (h₀ : x = 2 * t + 1)
  (h₁ : y = 2 * t - 1)
  (h₂ : z = 3 * t + 2)
  (h₃ : 0 < t) :
  x * y + y * z + z * x ≥ 16 * t^2 + 8 * t - 1   :=  by sorry
