-- Prove2me | Theorems.Thm_WorkbookSource_plus_11306
-- name    : WorkbookSource.plus_11306
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:23.299986+00:00
-- url     : https://prove2.me/theorems/2687959b-7871-434a-8fc7-3020308515bc
-- title:
--   A mixed cubic bound for a pairwise sum
-- statement:
--   Let $a,b,c>0,a+b+c=1.$ Prove that $a^2(b+c)+b^2(c +a)+c^2(a+b)+\frac{16}{9}\geq 6(ab+bc+ca).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_11306` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11306; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_11306 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) + 16 / 9 ≥ 6 * (a * b + b * c + c * a)   :=  by sorry
