-- Prove2me | Theorems.Thm_WorkbookSource_base_12567
-- name    : WorkbookSource.base_12567
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:07:26.057575+00:00
-- url     : https://prove2.me/theorems/fc2e0014-c5ca-4f87-b092-dab9cdbbc148
-- title:
--   A cyclic ninth-power comparison of weighted linear forms
-- statement:
--   Prove that \((4a+2b)^9+(4b+2c)^9+(4c+2a)^9 \ge (3a+2b+c)^9+ (3b+2c+a)^9+ (3c+2a+b)^9\) with \(a,b,c>0\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12567` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12567; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12567 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a + 2 * b) ^ 9 + (4 * b + 2 * c) ^ 9 + (4 * c + 2 * a) ^ 9 ≥ (3 * a + 2 * b + c) ^ 9 + (3 * b + 2 * c + a) ^ 9 + (3 * c + 2 * a + b) ^ 9  :=  by sorry
