-- Prove2me | Theorems.Thm_lean_workbook_plus_57277
-- name    : lean_workbook_plus_57277
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d817d156-3215-4067-8467-c08e5c0b8d1e
-- statement:
--   Prove that for all real numbers $x, y, z$ \n $$5 (x^2 + y^2 + z^2) \geq4 (xy + yz + zx).$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57277 (x y z : ℝ) : 5 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 4 * (x * y + y * z + z * x)   :=  by sorry
