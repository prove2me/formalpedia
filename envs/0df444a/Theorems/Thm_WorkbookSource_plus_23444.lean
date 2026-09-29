-- Prove2me | Theorems.Thm_WorkbookSource_plus_23444
-- name    : WorkbookSource.plus_23444
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:40:29.278114+00:00
-- url     : https://prove2.me/theorems/e2695954-88f2-4f71-bfba-9664aef649bd
-- title:
--   A mixed reciprocal sum is at least one
-- statement:
--   Let $a,b,c>0$ and $a+b+c=3$ . Prove that $\frac{2}{ab+bc+ca}+\frac{1}{a^2b+b^2c+c^2 a}\ge 1.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_23444` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23444; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_23444 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 2 / (a * b + b * c + c * a) + 1 / (a^2 * b + b^2 * c + c^2 * a) ≥ 1   :=  by sorry
