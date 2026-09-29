-- Prove2me | Theorems.Thm_lean_workbook_plus_53745
-- name    : lean_workbook_plus_53745
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d9499401-e0a4-452c-aa0a-2df59e438c1b
-- statement:
--   By Cauchy-Schwarz Inequality, we have \n $\begin{aligned}2(x^2+y^2)(y^2+z^2)(z^2+x^2)&=[(x+y)^2+(x-y)^2][(xy+z^2)^2+z^2(x-y)^2] \&\geqslant [(x+y)(xy+z^2)+z(x-y)]^2\&=[xy(x+y)+yz(y+z)+zx(z+x)-2xyz]^2.\end{aligned}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53745  (x y z : ℝ) :
  2 * (x^2 + y^2) * (y^2 + z^2) * (z^2 + x^2) ≥ (x * y * (x + y) + y * z * (y + z) + z * x * (z + x) - 2 * x * y * z)^2   :=  by sorry
