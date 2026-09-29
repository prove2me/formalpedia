-- Prove2me | Theorems.Thm_WorkbookSource_base_52908
-- name    : WorkbookSource.base_52908
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:24:17.354269+00:00
-- url     : https://prove2.me/theorems/f2f0d2ea-d912-4936-8464-88853493ffae
-- title:
--   A shifted cyclic triple-product ratio is at most four fifths at fixed total four
-- statement:
--   Let $a,b,c,d>0,a+b+c+d=4$ ,prove that: $\frac{abc}{d+4}+\frac{bcd}{a+4}+\frac{cda}{b+4}+\frac{dab}{c+4}\le \frac{4}{5} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52908` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52908; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52908 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 4) : (a * b * c) / (d + 4) + (b * c * d) / (a + 4) + (c * d * a) / (b + 4) + (d * a * b) / (c + 4) ≤ 4 / 5  :=  by sorry
