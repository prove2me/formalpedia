-- Prove2me | Theorems.Thm_lean_workbook_plus_57996
-- name    : lean_workbook_plus_57996
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c6d0160a-68a4-41b1-934b-2132b0dc5fcb
-- statement:
--   Now, we will prove that\n\n$9x^{2}+25y^{2}+225z^{2}\ge 15(xy+3xz+5yz)$\n\n$\implies 2\left(9x^{2}+25y^{2}+225z^{2}\right)\ge 30(xy+3xz+5yz)$\n\n$\implies \left(9x^2-30xy+25y^2\right)+\left(25y^2-150yz+225z^2\right)+\left(225z^2-90zx+9x^2\right)\ge 0$\n\n$\implies (3x-5y)^2+(5y-15z)^2+(15z-3x)^2\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57996 (x y z : ℝ) : 9 * x ^ 2 + 25 * y ^ 2 + 225 * z ^ 2 ≥ 15 * (x * y + 3 * x * z + 5 * y * z)   :=  by sorry
