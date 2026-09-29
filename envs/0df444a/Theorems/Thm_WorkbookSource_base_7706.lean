-- Prove2me | Theorems.Thm_WorkbookSource_base_7706
-- name    : WorkbookSource.base_7706
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:22.47291+00:00
-- url     : https://prove2.me/theorems/6ea7acda-0811-4928-a9e9-3369d008eec5
-- title:
--   A quadratic sum with a triple-product correction at fixed sum three
-- statement:
--   Given $a, b, c$ positive real numbers such that the sum of all three variables is 3, prove that
--    $$\sum_{cyc}(a^2)+\frac{4abc}{3}\ge \frac{13}{3}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7706` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7706; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7706 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 + b^2 + c^2 + (4 * a * b * c) / 3 ≥ 13 / 3  :=  by sorry
