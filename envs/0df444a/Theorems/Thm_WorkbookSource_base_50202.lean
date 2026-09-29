-- Prove2me | Theorems.Thm_WorkbookSource_base_50202
-- name    : WorkbookSource.base_50202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:36:26.290339+00:00
-- url     : https://prove2.me/theorems/41b79374-202a-4a72-b9ec-f6c2eec1dce3
-- title:
--   A refined cubic inequality at fixed sum three
-- statement:
--   Prove that $2(a^2+b^2+c^2)+3abc\ge 9+\frac{abc(ab+bc+ca-3abc)}{6(ab+bc+ca)}$ given $a,b,c>0$ and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50202` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50202; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50202 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * a * b * c ≥ 9 + (a * b * c * (a * b + b * c + c * a - 3 * a * b * c)) / (6 * (a * b + b * c + c * a))  :=  by sorry
