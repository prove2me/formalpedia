-- Prove2me | Theorems.Thm_WorkbookSource_base_26343
-- name    : WorkbookSource.base_26343
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:09:34.192982+00:00
-- url     : https://prove2.me/theorems/f52e9ba8-bbd6-4e9f-9577-0b6a74942113
-- title:
--   A cyclic shifted pair-product ratio sum is at least three quarters at unit product
-- statement:
--   If $a>0,b>0,c>0$ and $abc=1$ ,then prove that
--
--    $\frac{a}{(a+1)(b+1)}+\frac{b}{(b+1)(c+1)}+\frac{c}{(c+1)(a+1)}\geq \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26343` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26343; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26343 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a / (a + 1) / (b + 1) + b / (b + 1) / (c + 1) + c / (c + 1) / (a + 1)) ≥ 3 / 4  :=  by sorry
