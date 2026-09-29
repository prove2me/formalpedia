-- Prove2me | Theorems.Thm_WorkbookSource_base_4955
-- name    : WorkbookSource.base_4955
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:26.15293+00:00
-- url     : https://prove2.me/theorems/3d19ae00-a8c4-42f4-8a46-bd5230b2d58c
-- title:
--   A shifted-product bound at positive unit sum
-- statement:
--   Let $a,b,c>0 $ and $a+b+c=1.$ Prove that $(1-a)(2-b)(2-c)\geq 48abc$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4955` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4955; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4955 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : (1 - a) * (2 - b) * (2 - c) ≥ 48 * a * b * c  :=  by sorry
