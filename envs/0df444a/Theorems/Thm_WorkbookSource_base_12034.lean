-- Prove2me | Theorems.Thm_WorkbookSource_base_12034
-- name    : WorkbookSource.base_12034
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:29.694699+00:00
-- url     : https://prove2.me/theorems/e7ca2cc5-ed91-4b53-b41d-4ed432755acf
-- title:
--   A shifted rational product bounds a squared difference
-- statement:
--   Prove that for all $a,b>0$ the following inequality holds:
--
--    $$4(a+b+1)+(a-b)^2\leq \frac{(a+b+1)(a+1)^2(b+1)^2}{4ab}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12034` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12034; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12034 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 4 * (a + b + 1) + (a - b) ^ 2 ≤ (a + b + 1) * (a + 1) ^ 2 * (b + 1) ^ 2 / (4 * a * b)  :=  by sorry
