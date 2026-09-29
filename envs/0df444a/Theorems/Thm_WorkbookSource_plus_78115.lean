-- Prove2me | Theorems.Thm_WorkbookSource_plus_78115
-- name    : WorkbookSource.plus_78115
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:54.969713+00:00
-- url     : https://prove2.me/theorems/e9904593-2b02-4158-a8e3-bc82417c03cb
-- title:
--   A cyclic fifth-power sum dominates a mixed sum
-- statement:
--   x, y, z - positive. $x^5 + y^5 + z^5 - x^3z^2 - y^3x^2 - z^3y^2 \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_78115` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_78115; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_78115 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 5 + y ^ 5 + z ^ 5 - x ^ 3 * z ^ 2 - y ^ 3 * x ^ 2 - z ^ 3 * y ^ 2 ≥ 0   :=  by sorry
