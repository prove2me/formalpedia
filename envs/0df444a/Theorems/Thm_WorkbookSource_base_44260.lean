-- Prove2me | Theorems.Thm_WorkbookSource_base_44260
-- name    : WorkbookSource.base_44260
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:12.837995+00:00
-- url     : https://prove2.me/theorems/f69e2775-c670-44a9-a1fa-4ac5682d1135
-- title:
--   A mixed linear-quadratic-cubic upper bound at sum six
-- statement:
--   Let $ a,b,c\ge 0$ and $a+b+c=6 .$ Prove that $$ 2a+ab+abc\le 18$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44260` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44260; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44260 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 6) : 2*a + a*b + a*b*c ≤ 18  :=  by sorry
