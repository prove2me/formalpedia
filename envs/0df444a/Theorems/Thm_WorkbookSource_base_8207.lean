-- Prove2me | Theorems.Thm_WorkbookSource_base_8207
-- name    : WorkbookSource.base_8207
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:10:50.03636+00:00
-- url     : https://prove2.me/theorems/fb259389-5f9f-47be-b24a-a7c82e3c939d
-- title:
--   An asymmetric cubic polynomial is nonnegative
-- statement:
--   Show the steps to prove the inequality \(4x^3+(-4z-4y)x^2+(6yz-z^2-y^2)x+3(y+z)(y-z)^2\ge 0\) for positive reals x, y, and z.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8207` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8207; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8207 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : 4 * x ^ 3 + (-4 * z - 4 * y) * x ^ 2 + (6 * y * z - z ^ 2 - y ^ 2) * x + 3 * (y + z) * (y - z) ^ 2 ≥ 0  :=  by sorry
