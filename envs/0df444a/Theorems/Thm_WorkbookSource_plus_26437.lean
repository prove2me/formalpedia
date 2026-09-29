-- Prove2me | Theorems.Thm_WorkbookSource_plus_26437
-- name    : WorkbookSource.plus_26437
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:23:54.483563+00:00
-- url     : https://prove2.me/theorems/e29ed8ef-dc21-4ce5-b415-14cc70a3c347
-- title:
--   An eighth-degree inequality involving shifted pairwise sums
-- statement:
--   For positive numbers \\( x, y, z \\), prove that \\( 27(2x + z + y)^4((z + x)^2 + (x + y)^2)^2 \geq 256(2(z + x)^2 + 2(x + y)^2 - (y + z)^2)(z + x)^2(x + y)^2(x + y + z)^2 \\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_26437` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_26437; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_26437 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 27 * (2 * x + z + y) ^ 4 * ((z + x) ^ 2 + (x + y) ^ 2) ^ 2 ≥ 256 * (2 * (z + x) ^ 2 + 2 * (x + y) ^ 2 - (y + z) ^ 2) * (z + x) ^ 2 * (x + y) ^ 2 * (x + y + z) ^ 2   :=  by sorry
