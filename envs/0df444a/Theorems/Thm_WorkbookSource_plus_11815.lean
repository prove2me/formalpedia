-- Prove2me | Theorems.Thm_WorkbookSource_plus_11815
-- name    : WorkbookSource.plus_11815
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:38.45055+00:00
-- url     : https://prove2.me/theorems/359f25a6-c417-4e0f-9982-e62df01434b6
-- title:
--   A fourth-power sum minus four times the product bounds a squared-difference product
-- statement:
--   Let $a,b,c,d>0$ . Prove that $$a^4+b^4+c^4+d^4-4abcd\geq 2(a-b)^2(c-d)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_11815` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11815; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_11815 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d ≥ 2 * (a - b) ^ 2 * (c - d) ^ 2   :=  by sorry
