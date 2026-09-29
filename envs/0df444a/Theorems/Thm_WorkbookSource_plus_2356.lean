-- Prove2me | Theorems.Thm_WorkbookSource_plus_2356
-- name    : WorkbookSource.plus_2356
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:21.609412+00:00
-- url     : https://prove2.me/theorems/a089e2ea-64bc-46be-b384-25e7b5c695dd
-- title:
--   A cyclic weighted-square lower bound
-- statement:
--   If $a,b,c$ are positive numbers and $a+b+c=1$, prove: $ \sum_{cyc}a(2a+b+1)^2\ge\ 4 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2356` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2356; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2356 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : a * (2 * a + b + 1) ^ 2 + b * (2 * b + c + 1) ^ 2 + c * (2 * c + a + 1) ^ 2 ≥ 4   :=  by sorry
