-- Prove2me | Theorems.Thm_lean_workbook_plus_80816
-- name    : lean_workbook_plus_80816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5b8d2aea-127e-464a-b482-59ed2e41c023
-- statement:
--   Let $x,y,z >0$ Prove \n $(\sum x^2y^2)\ge (\sum xy)^2/3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80816 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ≥ (x * y + y * z + z * x)^2 / 3   :=  by sorry
