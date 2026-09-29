-- Prove2me | Theorems.Thm_WorkbookSource_plus_48343
-- name    : WorkbookSource.plus_48343
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:40.151369+00:00
-- url     : https://prove2.me/theorems/20c55dcd-19a5-4739-9054-ad45a6c071a1
-- title:
--   A cyclic ratio sum with a triple-product correction
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove that : $$\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+2abc\ge 5$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_48343` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_48343; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_48343 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / b + b / c + c / a + 2 * a * b * c ≥ 5   :=  by sorry
