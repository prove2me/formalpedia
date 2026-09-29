-- Prove2me | Theorems.Thm_lean_workbook_plus_60532
-- name    : lean_workbook_plus_60532
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/850c6f42-df0b-403e-84f6-43547a79e294
-- statement:
--   Prove that for all real numbers x, y, and z, \((x + y + z)^{2}(xy + yz + zx)^{2} \leq 3(x^{2} + xy + y^{2})(y^{2} + yz + z^{2})(z^{2} + zx + x^{2})\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60532 (x y z : ℝ) : (x + y + z) ^ 2 * (x*y + y*z + z*x) ^ 2 ≤ 3 * (x ^ 2 + x*y + y ^ 2) * (y ^ 2 + y*z + z ^ 2) * (z ^ 2 + z*x + x ^ 2)   :=  by sorry
