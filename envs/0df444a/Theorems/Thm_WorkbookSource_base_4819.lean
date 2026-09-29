-- Prove2me | Theorems.Thm_WorkbookSource_base_4819
-- name    : WorkbookSource.base_4819
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:33:24.1549+00:00
-- url     : https://prove2.me/theorems/e10a93c3-48bf-466d-a567-183eab514463
-- title:
--   A reciprocal pairwise-sum lower bound
-- statement:
--   Prove that for all positive real numbers $x, y, z$ the following inequality holds:
--
--    $\frac 1{x + y} + \frac 1{y + z} + \frac 1{z + x} \ge \frac {15 (x + y + z)}{2(x^2 + y^2 + z^2) + 8 (xy + yz + zx)}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4819` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4819; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4819 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 15 * (x + y + z) / (2 * (x ^ 2 + y ^ 2 + z ^ 2) + 8 * (x * y + y * z + z * x))  :=  by sorry
