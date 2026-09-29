-- Prove2me | Theorems.Thm_lean_workbook_plus_79982
-- name    : lean_workbook_plus_79982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1c03560f-ff2b-4972-b481-35236f6c3928
-- statement:
--   Let $x$ , $y$ , and $z$ be positive real numbers simultaenously satisfying\n$x(y^2+yz+z^2)=3y+10z$\n$y(z^2+zx+x^2)=21z+24x$\n$z(x^2+xy+y^2)=7x+28y$\nFind $xy+yz+xz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79982 (x y z : ℝ) : (x > 0 ∧ y > 0 ∧ z > 0 ∧ x * (y * y + y * z + z * z) = 3 * y + 10 * z ∧ y * (z * z + z * x + x * x) = 21 * z + 24 * x ∧ z * (x * x + x * y + y * y) = 7 * x + 28 * y) → x * y + y * z + z * x = 31   :=  by sorry
