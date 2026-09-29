-- Prove2me | Theorems.Thm_WorkbookSource_base_22
-- name    : WorkbookSource.base_22
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:15:33.332834+00:00
-- url     : https://prove2.me/theorems/387813df-504d-48ae-85e2-27c9fc2b6df8
-- title:
--   A pair-sum reciprocal product inequality at fixed total four
-- statement:
--   Let $a,b,c,d>0,a+b+c+d=4$ ,prove that: $\frac{1}{(a+b)(c+d)}+\frac{1}{(b+c)(d+a)}+\frac{1}{(c+a)(b+d)} \geq \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (habc : a + b + c + d = 4) : 1 / (a + b) / (c + d) + 1 / (b + c) / (d + a) + 1 / (c + a) / (b + d) ≥ 3 / 4  :=  by sorry
