-- Prove2me | Theorems.Thm_lean_workbook_plus_40426
-- name    : lean_workbook_plus_40426
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ae758f45-16aa-4f55-9f0b-27408542c008
-- statement:
--   Prove that $ \left\|\begin{array}{c} \{x,y,z\}\subset (0,\infty ) \ \ xy + yz + zx = 1\end{array}\right\|$ $ \Longrightarrow$ $ \boxed {\sum x(y^2 + z^2)(x^2 - yz)\ge 0}\ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40426 (x y z : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z) (h : x * y + y * z + z * x = 1) :
  x * (y^2 + z^2) * (x^2 - y * z) + y * (z^2 + x^2) * (y^2 - z * x) + z * (x^2 + y^2) * (z^2 - x * y) ≥ 0   :=  by sorry
