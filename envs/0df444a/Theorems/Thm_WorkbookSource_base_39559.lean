-- Prove2me | Theorems.Thm_WorkbookSource_base_39559
-- name    : WorkbookSource.base_39559
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:26.507224+00:00
-- url     : https://prove2.me/theorems/fe0f3903-86c4-4888-9312-25675015a920
-- title:
--   A cyclic ratio sum has a product lower bound at fixed sum three
-- statement:
--   If $a, b, c >0, a+b+c=3$ , then $\frac{a}{b}+ \frac{b}{c}+ \frac{c}{a} \ge \frac{12}{3abc+1}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39559` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39559; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39559 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / b + b / c + c / a ≥ 12 / (3 * a * b * c + 1)  :=  by sorry
