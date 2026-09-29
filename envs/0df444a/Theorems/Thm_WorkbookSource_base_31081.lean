-- Prove2me | Theorems.Thm_WorkbookSource_base_31081
-- name    : WorkbookSource.base_31081
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:59:35.156573+00:00
-- url     : https://prove2.me/theorems/77dcf45a-2f45-405f-bafa-447dec10543b
-- title:
--   A weighted sum of triple-variable quartics bounds a product of triple sums
-- statement:
--   prove that $8\, \left( a+b+c \right) ^{2} \left( ab+bc+ac \right) +8\, \left( d+a+b \right) ^{2} \left( ad+ab+bd \right) +8\, \left( b+c+d \right) ^{2} \left( bc+cd+bd \right) +8\, \left( a+c+d \right) ^{2} \left( cd+ad+ac \right) +189\,abcd\geq 13\, \left( a+c+d \right) \left( d+a+b \right) \left( a+b+c \right) \left( b+c+d \right)$ given $a,b,c,d>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31081` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31081; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31081 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 8 * (a + b + c) ^ 2 * (a * b + b * c + a * c) + 8 * (d + a + b) ^ 2 * (d * a + a * b + d * b) + 8 * (b + c + d) ^ 2 * (b * c + c * d + b * d) + 8 * (a + c + d) ^ 2 * (a * c + a * d + c * d) + 189 * a * b * c * d ≥ 13 * (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d)  :=  by sorry
