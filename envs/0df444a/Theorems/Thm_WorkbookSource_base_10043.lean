-- Prove2me | Theorems.Thm_WorkbookSource_base_10043
-- name    : WorkbookSource.base_10043
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:55.336133+00:00
-- url     : https://prove2.me/theorems/ce3669fa-6683-45c8-8ed2-23ad5f594ef9
-- title:
--   A cyclic squared ratio sum with a triple-product correction
-- statement:
--   Prove that if a,b,c>0, then:
--    $ \frac{a^2}{(a+b)^2}+\frac{b^2}{(b+c)^2}+\frac{c^2}{(c+a)^2}+\frac{2abc}{(b+c)(c+a)(a+b)}$ ≥1
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10043` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10043; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10043 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (a + b)^2 + b^2 / (b + c)^2 + c^2 / (c + a)^2 + (2 * a * b * c) / ((b + c) * (c + a) * (a + b))) ≥ 1  :=  by sorry
