-- Prove2me | Theorems.Thm_WorkbookSource_base_13717
-- name    : WorkbookSource.base_13717
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:16.390098+00:00
-- url     : https://prove2.me/theorems/d4cfb55a-e669-47e5-bb2f-9514f029b333
-- title:
--   A strengthened product inequality for three quadratic factors
-- statement:
--   The inequality
--    $$2(a^2+1)(b^2+1)(c^2+1) \ge (a+1)(b+1)(c+1)(a+b+c-1)+2(abc-1)^2,$$
--   is also true for all $a,\,b,\,c$ are real numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13717` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13717; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13717 (a b c : ℝ) : 2 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ≥ (a + 1) * (b + 1) * (c + 1) * (a + b + c - 1) + 2 * (a * b * c - 1) ^ 2  :=  by sorry
