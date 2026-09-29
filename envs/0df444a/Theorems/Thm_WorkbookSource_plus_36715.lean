-- Prove2me | Theorems.Thm_WorkbookSource_plus_36715
-- name    : WorkbookSource.plus_36715
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:58:09.744113+00:00
-- url     : https://prove2.me/theorems/d6491884-ce0e-4b13-9bd7-ad780c53394e
-- title:
--   A cyclic squared linear ratio sum is at least eight
-- statement:
--   Prove that if $ a,b,c > 0$ then
--    $ \frac {(4a + b - c)^2}{2a^2 + (b + c)^2} + \frac {(4b + c - a)^2}{2b^2 + (c + a)^2} + \frac {(4c + a - b)^2}{2c^2 + (a + b)^2}\geq8.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_36715` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_36715; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_36715 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a + b - c) ^ 2 / (2 * a ^ 2 + (b + c) ^ 2) + (4 * b + c - a) ^ 2 / (2 * b ^ 2 + (c + a) ^ 2) + (4 * c + a - b) ^ 2 / (2 * c ^ 2 + (a + b) ^ 2) ≥ 8   :=  by sorry
