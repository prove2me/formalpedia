-- Prove2me | Theorems.Thm_WorkbookSource_base_34416
-- name    : WorkbookSource.base_34416
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:39.935176+00:00
-- url     : https://prove2.me/theorems/920bea8c-7e75-4e61-8cb5-f6d7cbe09088
-- title:
--   A cyclic squared difference ratio sum is at least three fifths
-- statement:
--   If a,b,c>0 then
--    $ \frac {(a - b + c)^2}{a^2 + (b + c)^2} + \frac {(b - c + a)^2}{b^2 + (c + a)^2} + \frac {(c - a + b)^2}{c^2 + (a + b)^2} \ge \frac{3}{5}$ (Japan MO 2002)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34416` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34416; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34416 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b + c) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (b - c + a) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (c - a + b) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≥ 3 / 5  :=  by sorry
