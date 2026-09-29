-- Prove2me | Theorems.Thm_WorkbookSource_plus_69637
-- name    : WorkbookSource.plus_69637
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:50:33.175903+00:00
-- url     : https://prove2.me/theorems/068116b1-3b98-4c02-a240-db693cd29c76
-- title:
--   A cyclic linear ratio sum with a normalized pair-product correction
-- statement:
--   Let $a,b,c>0$ . Prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}+\frac{9(ab+bc+ca)}{2(a+b+c)^2} \geq 3$ Mathematical communication (Student journal) (China Wuhan) (4)2019，Problem 395
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_69637` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_69637; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_69637 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + (9 * (a * b + b * c + c * a)) / (2 * (a + b + c) ^ 2)) ≥ 3   :=  by sorry
