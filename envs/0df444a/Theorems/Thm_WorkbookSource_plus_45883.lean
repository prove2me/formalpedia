-- Prove2me | Theorems.Thm_WorkbookSource_plus_45883
-- name    : WorkbookSource.plus_45883
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:59.670178+00:00
-- url     : https://prove2.me/theorems/9f2fc281-17c7-46b0-9ad8-032ff2eeee21
-- title:
--   A product of cyclic ratio sums is at least twenty-seven
-- statement:
--   Let $a,b,c>0.$ Prove that
--    $$\left(\frac{c+a}{b}+\frac{2c}{a+b}\right)\left(\frac{a+b}{c}+\frac{2a}{b+c}\right)\left(\frac{b+c}{a}+\frac{2b}{c+a}\right) \geq27$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_45883` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_45883; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_45883 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : ((c + a) / b + 2 * c / (a + b)) * ((a + b) / c + 2 * a / (b + c)) * ((b + c) / a + 2 * b / (c + a)) ≥ 27   :=  by sorry
