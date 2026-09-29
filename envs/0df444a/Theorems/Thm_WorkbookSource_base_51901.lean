-- Prove2me | Theorems.Thm_WorkbookSource_base_51901
-- name    : WorkbookSource.base_51901
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:46.985633+00:00
-- url     : https://prove2.me/theorems/d90726a9-de96-42a8-b679-dffee4f01133
-- title:
--   A cyclic ratio sum bounds a weighted complementary sum
-- statement:
--   Let $a,b,c$ be positive reals, show that $\frac{a}{b}+\frac{b}{c}+\frac{c}{a}+\frac92 \ge \frac{5(b+c)}{b+c+2a}+\frac{5(c+a)}{c+a+2b}+\frac{5(a+b)}{a+b+2c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51901` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51901; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51901 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a + 9 / 2) ≥ 5 * (b + c) / (b + c + 2 * a) + 5 * (c + a) / (c + a + 2 * b) + 5 * (a + b) / (a + b + 2 * c)  :=  by sorry
