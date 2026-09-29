-- Prove2me | Theorems.Thm_lean_workbook_plus_7257
-- name    : lean_workbook_plus_7257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/156c52a7-8497-45e5-a31e-b112968feb67
-- statement:
--   for #5 \nWith condition $x+y+z=2$ ,we have \n $2(xy+yz+zx)(1+6xyz)-25xyz=y(2y-1)^2(x-z)^2+z(2z-1)^2(x-y)^2+x(2x-1)^2(y-z)^2$ \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7257 {x y z : ℝ} (h : x + y + z = 2) : 2 * (x * y + y * z + z * x) * (1 + 6 * x * y * z) - 25 * x * y * z = y * (2 * y - 1) ^ 2 * (x - z) ^ 2 + z * (2 * z - 1) ^ 2 * (x - y) ^ 2 + x * (2 * x - 1) ^ 2 * (y - z) ^ 2   :=  by sorry
