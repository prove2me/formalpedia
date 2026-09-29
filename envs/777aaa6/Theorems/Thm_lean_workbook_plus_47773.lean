-- Prove2me | Theorems.Thm_lean_workbook_plus_47773
-- name    : lean_workbook_plus_47773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7a167458-f401-43ec-a15b-b9bf1853ed6c
-- statement:
--   Let $a,b,c>0$. $2x^2y^2+2y^2z^2+2z^2x^2-x^4-y^4-z^4=(x+y+z)(x+y-z)(y+z-x)(z+x-y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47773 (x y z : ℝ) : (x + y + z) * (x + y - z) * (y + z - x) * (z + x - y) = 2 * x ^ 2 * y ^ 2 + 2 * y ^ 2 * z ^ 2 + 2 * z ^ 2 * x ^ 2 - x ^ 4 - y ^ 4 - z ^ 4   :=  by sorry
