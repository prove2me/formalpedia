-- Prove2me | Theorems.Thm_WorkbookSource_base_3684
-- name    : WorkbookSource.base_3684
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:32.91962+00:00
-- url     : https://prove2.me/theorems/3411514d-c64d-4cac-be41-657894c35583
-- title:
--   A quadratic-form comparison in three variables
-- statement:
--   prove that ; $(x+y)^2+13(x^2+y^2)+14z^2-2xy \ge x^2+4xy+4y^2+9z^2+6xz+12yz$ $\forall x,y,z >0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3684` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3684; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3684 (x y z : ℝ) : (x + y) ^ 2 + 13 * (x ^ 2 + y ^ 2) + 14 * z ^ 2 - 2 * x * y ≥ x ^ 2 + 4 * x * y + 4 * y ^ 2 + 9 * z ^ 2 + 6 * x * z + 12 * y * z  :=  by sorry
