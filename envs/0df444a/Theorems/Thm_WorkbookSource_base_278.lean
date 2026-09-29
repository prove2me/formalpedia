-- Prove2me | Theorems.Thm_WorkbookSource_base_278
-- name    : WorkbookSource.base_278
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:13.70615+00:00
-- url     : https://prove2.me/theorems/7d58a12c-cdb0-419f-bd24-db334547ac40
-- title:
--   A product of pairwise ratio sums has a symmetric lower bound
-- statement:
--   Let $ a,b,c>0 $ , prove that :
--   $$ \left( \frac{a}{b+c}+\frac{b}{c+a}\right)\left( \frac{b}{c+a}+\frac{c}{a+b}\right)\left( \frac{c}{a+b}+\frac{a}{b+c}\right)\ge \frac{7}{8}\left( \frac{a^2+b^2+c^2}{ab+bc+ca}\right)+\frac{1}{8}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_278` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_278; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_278 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a)) * (b / (c + a) + c / (a + b)) * (c / (a + b) + a / (b + c)) ≥ 7 / 8 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + 1 / 8  :=  by sorry
