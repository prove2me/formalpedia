-- Prove2me | Theorems.Thm_lean_workbook_plus_8204
-- name    : lean_workbook_plus_8204
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b7b0a5ef-40a2-41ee-9422-34d1be96ed83
-- statement:
--   $x^3 + y^3 + z^3 = 3xyz + (x+y+z)(x^2 + y^2 + z^2 - xy - yz - zx)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8204 (x y z : ℝ) : x^3 + y^3 + z^3 = 3 * x * y * z + (x + y + z) * (x^2 + y^2 + z^2 - x * y - y * z - z * x)   :=  by sorry
