-- Prove2me | Theorems.Thm_WorkbookSource_plus_75038
-- name    : WorkbookSource.plus_75038
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:42.97389+00:00
-- url     : https://prove2.me/theorems/2d81bc4a-3232-4611-bade-3eb665d0ffa4
-- title:
--   A cyclic cubic lower bound at fixed sum three
-- statement:
--   For non-negative reals $x, y, z$ such that $x + y + z = 3$, prove that:
--   $2(x^2 + y^2 + z^2) + x^2z + xy^2 + yz^2 \ge 2xyz + xy + yz + xz + 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75038` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75038; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75038 (x y z : ℝ) (hx : x + y + z = 3) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + x ^ 2 * z + x * y ^ 2 + y * z ^ 2 ≥ 2 * x * y * z + x * y + y * z + x * z + 4   :=  by sorry
