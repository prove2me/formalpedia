-- Prove2me | Theorems.Thm_lean_workbook_plus_68311
-- name    : lean_workbook_plus_68311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/8c1fc1fa-f18b-43fd-9998-17f549682400
-- statement:
--   Prove that for all real numbers $x, y, z$ \n $$5 (x^2 + y^2 + z^2) - 4 (xy + yz + zx) = (2x- y)^2 + (2y - z)^2 + (2z - x)^2.$$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68311 (x y z : ℝ) : 5 * (x ^ 2 + y ^ 2 + z ^ 2) - 4 * (x * y + y * z + z * x) = (2 * x - y) ^ 2 + (2 * y - z) ^ 2 + (2 * z - x) ^ 2   :=  by sorry
