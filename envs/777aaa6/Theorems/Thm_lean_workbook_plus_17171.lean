-- Prove2me | Theorems.Thm_lean_workbook_plus_17171
-- name    : lean_workbook_plus_17171
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/457330bf-a3ac-4a62-b68a-b31e359c749d
-- statement:
--   It is given to make use of the identity- \n $ (ax + by +cz )^{2} + (ay-bx)^{2} + (bz-cy)^{2} + (cx-az)^{2} = (a^{2} +b^{2}+c^{2})(x^{2} +y^{2}+z^{2}) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17171 (a b c x y z : ℝ) : (a * x + b * y + c * z) ^ 2 + (a * y - b * x) ^ 2 + (b * z - c * y) ^ 2 + (c * x - a * z) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)   :=  by sorry
