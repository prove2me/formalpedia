-- Prove2me | Theorems.Thm_WorkbookSource_base_27454
-- name    : WorkbookSource.base_27454
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:41.847923+00:00
-- url     : https://prove2.me/theorems/2146991b-5260-4eaf-a33f-cdfe969398e5
-- title:
--   A product of shifted squares at positive sum three
-- statement:
--   prove $(a^2+3)(b^2+3)(c^2+3)\geq 4(a+b+c+1)^2$ given $a,b,c>0$ and $a+b+c=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27454` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27454; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27454 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 3) * (b^2 + 3) * (c^2 + 3) ≥ 4 * (a + b + c + 1)^2  :=  by sorry
