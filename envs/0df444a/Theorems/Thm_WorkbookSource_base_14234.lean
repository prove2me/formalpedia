-- Prove2me | Theorems.Thm_WorkbookSource_base_14234
-- name    : WorkbookSource.base_14234
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:54:27.103681+00:00
-- url     : https://prove2.me/theorems/1d80f43c-4e63-4896-b9fc-a955f2bb9e09
-- title:
--   A normalized triple product bounded by symmetric quadratic forms
-- statement:
--   Prove that for all positive real numbers x, y, and z, the following inequality holds:
--   $\frac{8xyz}{(x+y)(y+z)(z+x)}\le \frac{3(x^{2}+y^{2}+z^{2}+3(xy+yz+zx))}{4(x+y+z)^{2}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14234` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14234; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14234 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (8 * x * y * z) / (x + y) / (y + z) / (z + x) ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2 + 3 * (x * y + y * z + z * x))) / (4 * (x + y + z) ^ 2)  :=  by sorry
