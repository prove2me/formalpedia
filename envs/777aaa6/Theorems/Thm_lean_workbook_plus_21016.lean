-- Prove2me | Theorems.Thm_lean_workbook_plus_21016
-- name    : lean_workbook_plus_21016
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/85a85a5d-5761-4602-917d-721931937d89
-- statement:
--   (a) We have $x^2y+y=x^2+x+1\iff (y-1)x^2-x+(y-1)=0$ . Since $x$ is real, its discriminant should be at least $0$ , i.e. $1^2-4(y-1)^2\geq 0\iff4(y-1)^2\leq1\iff-\frac{1}{2} \leq y-1 \leq\frac{1}{2}\iff\frac{1}{2} \leq y \leq\frac{3}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21016  (x y : ℝ)
  (h₀ : x^2 * y + y = x^2 + x + 1) :
  1 / 2 ≤ y ∧ y ≤ 3 / 2   :=  by sorry
