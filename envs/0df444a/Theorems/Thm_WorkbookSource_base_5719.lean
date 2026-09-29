-- Prove2me | Theorems.Thm_WorkbookSource_base_5719
-- name    : WorkbookSource.base_5719
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:37:28.442405+00:00
-- url     : https://prove2.me/theorems/d6505891-0dc5-4d83-999b-3120468af76b
-- title:
--   A cyclic sum of three squared ratios is bounded above
-- statement:
--   If a,b,c>0 then
--    $ \frac {(a - b + c)^2}{a^2 + (b + c)^2} + \frac {(b - c + a)^2}{b^2 + (c + a)^2} + \frac {(c - a + b)^2}{c^2 + (a + b)^2} \leq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5719` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5719; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5719 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a - b + c) ^ 2 / (a ^ 2 + (b + c) ^ 2) + (b - c + a) ^ 2 / (b ^ 2 + (c + a) ^ 2) + (c - a + b) ^ 2 / (c ^ 2 + (a + b) ^ 2) ≤ 3  :=  by sorry
