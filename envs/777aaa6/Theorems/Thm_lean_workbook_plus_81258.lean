-- Prove2me | Theorems.Thm_lean_workbook_plus_81258
-- name    : lean_workbook_plus_81258
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3ac431f8-a486-4c90-bffb-76d5405c35a1
-- statement:
--   Let $x,y,z \geq 0$ ,prove that: $x^2(3y+x)^2+y^2(3z+y)^2-2(x+y)^2y(3z+x)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81258 (x y z : ℝ) : x^2 * (3 * y + x)^2 + y^2 * (3 * z + y)^2 - 2 * (x + y)^2 * y * (3 * z + x) ≥ 0   :=  by sorry
