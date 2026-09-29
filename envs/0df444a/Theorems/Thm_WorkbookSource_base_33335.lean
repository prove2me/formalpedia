-- Prove2me | Theorems.Thm_WorkbookSource_base_33335
-- name    : WorkbookSource.base_33335
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:51:50.84314+00:00
-- url     : https://prove2.me/theorems/5dedd20a-dfa1-4646-8dc7-e1fe81017e46
-- title:
--   A product of mixed cyclic ratios is at least 343 over eight
-- statement:
--   Let $a,b,c>0.$ Prove that
--    $$ \left(\frac{c+2a}{b}+\frac{c}{a+b}\right)\left(\frac{a+2b}{c}+\frac{a}{b+c}\right)\left(\frac{b+2c}{a}+\frac{b}{c+a}\right)\geq \frac{343}{8}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33335` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33335; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33335 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : ((c + 2 * a) / b + c / (a + b)) * ((a + 2 * b) / c + a / (b + c)) * ((b + 2 * c) / a + b / (c + a)) ≥ 343 / 8  :=  by sorry
