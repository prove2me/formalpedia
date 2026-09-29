-- Prove2me | Theorems.Thm_lean_workbook_plus_74854
-- name    : lean_workbook_plus_74854
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/66eecaf5-40da-435c-884c-d10543853f57
-- statement:
--   $x^3+y^3+z^3 = (x+y+z)(x^2+y^2+z^2-xy-xz-yz)+3xyz \forall x,y,z \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74854 : ∀ x y z : ℝ, x^3 + y^3 + z^3 = (x + y + z) * (x^2 + y^2 + z^2 - x * y - x * z - y * z) + 3 * x * y * z   :=  by sorry
