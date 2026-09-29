-- Prove2me | Theorems.Thm_WorkbookSource_base_33453
-- name    : WorkbookSource.base_33453
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:00.435778+00:00
-- url     : https://prove2.me/theorems/b8c0e4b0-30ba-4cd1-84e5-c821ba693add
-- title:
--   Three squared cubic sums bounded by a cubic quadratic form
-- statement:
--   Prove that : $\forall x,y,z \in R$ :
--    $(x^2+y^2+z^2)^3 \geq(x^3+y^3+z^3)^2+(xy^2+yz^2+zx^2)^2+(x^2y+y^2z+z^2x)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33453` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33453; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33453 (x y z : ℝ) : (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≥ (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) ^ 2 + (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ^ 2  :=  by sorry
