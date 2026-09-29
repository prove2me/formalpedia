-- Prove2me | Theorems.Thm_lean_workbook_plus_30398
-- name    : lean_workbook_plus_30398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/74060a69-eba7-4537-9572-207db10f7d4d
-- statement:
--   Prove that $y = -\dfrac{x^2+2bx+c}{2a}, a\ne0$ is equivalent to $y = -\frac1{2a} \left(\left(x+b\right)^2 +\left(c-b^2\right)\right),a\ne0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30398 (a b c x y : ℝ) (ha : a ≠ 0) : y = -(x^2 + 2*b*x + c)/(2*a) ↔ y = -(1/(2*a)) * ((x + b)^2 + (c - b^2))   :=  by sorry
