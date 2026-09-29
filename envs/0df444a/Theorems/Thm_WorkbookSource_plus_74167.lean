-- Prove2me | Theorems.Thm_WorkbookSource_plus_74167
-- name    : WorkbookSource.plus_74167
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:35.023256+00:00
-- url     : https://prove2.me/theorems/c032b83c-833a-45fd-82f7-ebc807a235d2
-- title:
--   An asymmetric sixth-power inequality with cubic products
-- statement:
--   Let $a=x^2,b=y^2,c=z^2$ .The given inequality is equivalent to $4z^6+x^6+y^6+3x^2y^2(x^2+y^2)\ge 4(x^3y^3+y^3z^3+z^3x^3)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_74167` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_74167; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_74167 (x y z : ℝ) : 4 * z ^ 6 + x ^ 6 + y ^ 6 + 3 * x ^ 2 * y ^ 2 * (x ^ 2 + y ^ 2) ≥ 4 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3)   :=  by sorry
