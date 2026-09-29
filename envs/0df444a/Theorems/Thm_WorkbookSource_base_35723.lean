-- Prove2me | Theorems.Thm_WorkbookSource_base_35723
-- name    : WorkbookSource.base_35723
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:21.903355+00:00
-- url     : https://prove2.me/theorems/6320803d-31cc-4085-b9cf-1b1e70820531
-- title:
--   A two-variable quartic inequality with a shifted cubic factor
-- statement:
--   If $x,\,y$ are real numbers, then
--    $xy(x^2+y^2) \leqslant 2+\frac12 (x+y-2) (x+y)^3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35723` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35723; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35723 (x y : ℝ) : x * y * (x ^ 2 + y ^ 2) ≤ 2 + 1 / 2 * (x + y - 2) * (x + y) ^ 3  :=  by sorry
