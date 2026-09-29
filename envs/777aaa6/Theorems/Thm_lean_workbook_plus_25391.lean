-- Prove2me | Theorems.Thm_lean_workbook_plus_25391
-- name    : lean_workbook_plus_25391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d56d20a5-bae9-46dd-8bc6-4dc501718716
-- statement:
--   Prove that for $x,y,z\geq 0$, \n$(xy+xz+yz)(xy^2+yz^2+x^2z)-(x+y+z)^2xyz\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25391 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (x * y + x * z + y * z) * (x * y ^ 2 + y * z ^ 2 + x ^ 2 * z) - (x + y + z) ^ 2 * x * y * z ≥ 0   :=  by sorry
