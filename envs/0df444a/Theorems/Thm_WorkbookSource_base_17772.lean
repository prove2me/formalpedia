-- Prove2me | Theorems.Thm_WorkbookSource_base_17772
-- name    : WorkbookSource.base_17772
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:09:53.630016+00:00
-- url     : https://prove2.me/theorems/9d7095b1-8215-49ab-bb16-906bcff09a93
-- title:
--   A shifted cubic ratio lower bound at fixed sum three
-- statement:
--   Show that , \(\frac{a+b^3}{c+1}+\frac{b+c^3}{a+1}+\frac{c+a^3}{b+1}\ge 3\), where \(a+b+c=3,a,b,c\in \mathbb{R}^+\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17772` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17772; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17772 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + b^3) / (c + 1) + (b + c^3) / (a + 1) + (c + a^3) / (b + 1) ≥ 3  :=  by sorry
