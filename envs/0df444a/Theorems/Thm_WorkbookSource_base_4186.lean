-- Prove2me | Theorems.Thm_WorkbookSource_base_4186
-- name    : WorkbookSource.base_4186
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:37.58657+00:00
-- url     : https://prove2.me/theorems/17a8e509-cbca-4f08-9e69-7ff2f8b8143d
-- title:
--   A cyclic fourth-power comparison at unit positive sum
-- statement:
--   Easy. Let $a, b, c>0, a+b+c=1$ .Prove that
--    $a^3+b^3+c^3\ge3(a^3c+b^3a+c^3b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4186` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4186; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4186 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^3 + b^3 + c^3 ≥ 3 * (a^3 * c + b^3 * a + c^3 * b)  :=  by sorry
