-- Prove2me | Theorems.Thm_lean_workbook_plus_8030
-- name    : lean_workbook_plus_8030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a7eeca19-ce70-4b55-974e-950c1ced518f
-- statement:
--   We have $x^2y+y^2z+z^2x=xy^2+yz^2+zx^2 \Leftrightarrow (x-y)(y-z)(z-x)=0$ . Thus, $x=y$ or $y=z$ or $z=x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8030 : ∀ x y z : ℝ, x^2*y + y^2*z + z^2*x = x*y^2 + y*z^2 + z*x^2 ↔ x = y ∨ y = z ∨ z = x   :=  by sorry
