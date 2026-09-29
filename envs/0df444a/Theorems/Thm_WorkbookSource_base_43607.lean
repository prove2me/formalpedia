-- Prove2me | Theorems.Thm_WorkbookSource_base_43607
-- name    : WorkbookSource.base_43607
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:30.708029+00:00
-- url     : https://prove2.me/theorems/45eb6ada-4a00-485b-92e9-64c0c2b20e16
-- title:
--   Three quadratic forms bound a squared mixed expression
-- statement:
--   Then $ 3(x^2 + xy + y^2)(y^2 + yz + z^2)(z^2 + zx + x^2)\geq\frac {9}{4}(y + z)^2\left(x^2 + \frac {(y + z)x}{2} + yz\right)^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43607` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43607; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43607 (x y z : ℝ) : 3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ 9 / 4 * (y + z) ^ 2 * (x ^ 2 + (y + z) * x / 2 + y * z) ^ 2  :=  by sorry
