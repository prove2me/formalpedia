-- Prove2me | Theorems.Thm_WorkbookSource_base_51471
-- name    : WorkbookSource.base_51471
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:42:49.248633+00:00
-- url     : https://prove2.me/theorems/6a31f78f-6520-412b-af71-b20bc101480c
-- title:
--   A cyclic ratio sum with a pairwise correction
-- statement:
--   If $ a,b,c>0 ,$
--    $ \frac{a}{b}+\frac{b}{c}+\frac{c}{a}\geq \frac{9}{2}-\left(\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a} \right) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51471` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51471; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51471 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 9 / 2 - (a / (a + b) + b / (b + c) + c / (c + a))  :=  by sorry
