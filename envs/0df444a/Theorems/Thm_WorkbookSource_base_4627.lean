-- Prove2me | Theorems.Thm_WorkbookSource_base_4627
-- name    : WorkbookSource.base_4627
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:59.791408+00:00
-- url     : https://prove2.me/theorems/0a71e35e-cac3-42ec-8525-5ab235fc363c
-- title:
--   A cyclic ratio sum with a pairwise-product correction
-- statement:
--   Let $ a,b,c>0 .$
--    $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac{24abc}{(b+c)(c+a)(a+b)}\geq 6 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4627` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4627; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4627 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + 24 * a * b * c / (b + c) / (c + a) / (a + b)) ≥ 6  :=  by sorry
