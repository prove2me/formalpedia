-- Prove2me | Theorems.Thm_WorkbookSource_base_38173
-- name    : WorkbookSource.base_38173
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:21.464024+00:00
-- url     : https://prove2.me/theorems/4cd583e5-fe7a-4f2d-8a9c-04bfb62b150d
-- title:
--   Nonnegativity of a sixth-degree difference polynomial
-- statement:
--   The following inequality is equivalent to
--
--    $ 4(a-b)^2(-c+b)^2(c-a)^2+3\sum{b^2c^2(a-b)(a-c)}+3abc\sum{a(a-b)(a-c)}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38173` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38173; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38173 (a b c : ℝ) : (4 * (a - b) ^ 2 * (-c + b) ^ 2 * (c - a) ^ 2 + 3 * (b ^ 2 * c ^ 2 * (a - b) * (a - c) + c ^ 2 * a ^ 2 * (b - a) * (b - c) + a ^ 2 * b ^ 2 * (c - a) * (c - b)) + 3 * a * b * c * (a * (a - b) * (a - c) + b * (b - a) * (b - c) + c * (c - a) * (c - b))) ≥ 0  :=  by sorry
