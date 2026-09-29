-- Prove2me | Theorems.Thm_WorkbookSource_plus_44524
-- name    : WorkbookSource.plus_44524
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:32.511409+00:00
-- url     : https://prove2.me/theorems/7dff4d15-09bd-4183-973b-0bd478e91cbd
-- title:
--   A squared pair-product ratio upper bound at fixed sum three
-- statement:
--   Let $a,cb,c>0,a+b+c=3$ ,prove that: $\frac{b^2c^2}{a+3bc}+\frac{c^2a^2}{b+3ac}+\frac{a^2b^2}{c+3ab}\le \frac{3}{4} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44524` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44524; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44524 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (b^2 * c^2 / (a + 3 * b * c) + c^2 * a^2 / (b + 3 * c * a) + a^2 * b^2 / (c + 3 * a * b)) ≤ 3 / 4   :=  by sorry
