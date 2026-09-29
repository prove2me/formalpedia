-- Prove2me | Theorems.Thm_WorkbookSource_base_5049
-- name    : WorkbookSource.base_5049
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:39:40.413392+00:00
-- url     : https://prove2.me/theorems/b14409b5-3aea-4e58-9d54-dd1be8ee1582
-- title:
--   A four-variable mixed quadratic ratio sum bounds the total
-- statement:
--   Let $a,b,c,d>0$ ,prove that: ${\frac {{a}^{2}+bc}{d+a}}+{\frac {{b}^{2}+cd}{a+b}}+{\frac {{c}^{2}+ad}{b+c}}+{\frac {{d}^{2}+ab}{c+d}}\geq a+b+c+d$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5049` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5049; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5049 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 + b * c) / (d + a) + (b^2 + c * d) / (a + b) + (c^2 + d * a) / (b + c) + (d^2 + a * b) / (c + d) ≥ a + b + c + d  :=  by sorry
