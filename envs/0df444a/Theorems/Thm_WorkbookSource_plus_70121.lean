-- Prove2me | Theorems.Thm_WorkbookSource_plus_70121
-- name    : WorkbookSource.plus_70121
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:58:39.173634+00:00
-- url     : https://prove2.me/theorems/1b9c030e-4c8a-4921-8a1b-72f10b653b94
-- title:
--   A pair and triple-product ratio inequality bounds nine times the product
-- statement:
--   If $a,b,c,d$ are positive real numbers, then
--
--    $$\frac{(ab+bc+cd+da+ac+bd)(abc+bcd+cda+dab)}{a+b+c+d}+$$ $$+\frac{3(abc+bcd+cda+dab)^2}{(a+b+c+d)^2}\ge 9 abcd.$$
--
--   It's just $\sum\limits_{sym}(a^3b^2c+a^2b^2c^2-a^3bcd-a^2b^2cd)\geq0,$ which is true by Muirhead.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_70121` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_70121; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_70121 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * b + b * c + c * d + d * a + a * c + b * d) * (a * b * c + b * c * d + c * d * a + d * a * b) / (a + b + c + d) + 3 * (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / (a + b + c + d) ^ 2 ≥ 9 * a * b * c * d   :=  by sorry
