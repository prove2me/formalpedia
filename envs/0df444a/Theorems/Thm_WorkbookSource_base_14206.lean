-- Prove2me | Theorems.Thm_WorkbookSource_base_14206
-- name    : WorkbookSource.base_14206
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:54:22.000596+00:00
-- url     : https://prove2.me/theorems/7f549341-b9fd-4021-9eeb-27b9b12f56ea
-- title:
--   A weighted cyclic ratio lower bound with a triple-product correction
-- statement:
--   Let $a,b,c >0$ such that $a+b+c=3.$ Prove that $$ \frac{a+2b}{c} + \frac{b+2c}{a} + \frac{c+2a}{b} \ge 3(5-2abc)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14206` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14206; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14206 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + 2 * b) / c + (b + 2 * c) / a + (c + 2 * a) / b ≥ 3 * (5 - 2 * a * b * c)  :=  by sorry
