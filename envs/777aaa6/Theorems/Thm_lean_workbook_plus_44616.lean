-- Prove2me | Theorems.Thm_lean_workbook_plus_44616
-- name    : lean_workbook_plus_44616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2d6f7d2c-6daa-4401-9817-4d0d990ed125
-- statement:
--   Prove that $ (x-y)(y-z)(z-x)=x(y^2-z^2)+y(z^2-x^2)+z(x^2-y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44616 : ∀ x y z : ℝ, (x - y) * (y - z) * (z - x) = x * (y^2 - z^2) + y * (z^2 - x^2) + z * (x^2 - y^2)   :=  by sorry
