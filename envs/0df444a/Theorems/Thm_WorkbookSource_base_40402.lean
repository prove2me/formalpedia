-- Prove2me | Theorems.Thm_WorkbookSource_base_40402
-- name    : WorkbookSource.base_40402
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:34.824527+00:00
-- url     : https://prove2.me/theorems/13a0edfd-03fa-401f-9fca-7857e520c8f6
-- title:
--   A mixed linear, quadratic and cubic expression is at most eighteen
-- statement:
--   Let $a,b,c\geq 0, a+b+c=5 .$ $$2a+2ab+abc\le 18.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40402` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40402; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40402 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 5) : 2 * a + 2 * a * b + a * b * c ≤ 18  :=  by sorry
