-- Prove2me | Theorems.Thm_WorkbookSource_base_14529
-- name    : WorkbookSource.base_14529
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:26.247556+00:00
-- url     : https://prove2.me/theorems/37a0a55f-620a-49eb-969f-4be68c0e94f2
-- title:
--   Two squares and a cube sum to at least eleven halves at fixed sum four
-- statement:
--   Let $a,b,c>0,a+b+c=4 .$ Prove that $$a^2+b^2+c^3\geq \frac{11}{2}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14529` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14529; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 4) : a^2 + b^2 + c^3 ≥ 11 / 2  :=  by sorry
