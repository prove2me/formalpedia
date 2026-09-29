-- Prove2me | Theorems.Thm_WorkbookSource_base_9999
-- name    : WorkbookSource.base_9999
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:10:40.583853+00:00
-- url     : https://prove2.me/theorems/232153be-e99d-4539-8d02-9e0d4a4cf43c
-- title:
--   A reciprocal-total product inequality with a pair-product correction
-- statement:
--   $a,b,c,d>0$ ,prove
--
--    $ \left( a+b+c+d \right) \left( {\frac {1}{a}}+{\frac {1}{b}}+{\frac {1}{c}}+{\frac {1}{d}} \right) +8\geq 9\,{\frac { \left( a+b+c+d \right) ^{2}}{ab+bc+cd+ad+ac+bd}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9999` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9999; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9999 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) + 8 ≥ 9 * (a + b + c + d) ^ 2 / (a * b + b * c + c * d + a * d + a * c + b * d)  :=  by sorry
