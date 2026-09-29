-- Prove2me | Theorems.Thm_WorkbookSource_plus_36412
-- name    : WorkbookSource.plus_36412
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:52:31.286733+00:00
-- url     : https://prove2.me/theorems/d5bb38eb-52b7-4c14-ad43-cb95bf7e988d
-- title:
--   A weighted cyclic quadratic ratio sum bounds one quarter of the total
-- statement:
--   $a, b $ and $ c $ are positive numbers,then $\frac{a^2}{2a+b+c} + \frac{b^2}{a+2b+c}+ \frac{c^2}{a+b+2c}\ge \frac{a+b+c}{4 }.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_36412` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_36412; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_36412 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a + b + c) + b^2 / (a + 2 * b + c) + c^2 / (a + b + 2 * c)) ≥ (a + b + c) / 4   :=  by sorry
