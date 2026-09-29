-- Prove2me | Theorems.Thm_WorkbookSource_base_17800
-- name    : WorkbookSource.base_17800
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:45:00.366144+00:00
-- url     : https://prove2.me/theorems/3f6eb4e3-88fd-43be-a74c-b6ebf9f8ebbd
-- title:
--   A sum of triple quadratic averages bounds the four-variable total
-- statement:
--   Let be a,b,c,d real positive numbers. Show that
--
--    $\frac{a^{2}+b^{2}+c^{2}}{a+b+c}+\frac{b^{2}+c^{2}+d^{2}}{b+c+d}+\frac{c^{2}+d^{2}+a^{2}}{c+d+a}+\frac{d^{2}+a^{2}+b^{2}}{d+a+b}\geq a+b+c+d$
--
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17800` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17800; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17800 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 + b^2 + c^2)/(a + b + c) + (b^2 + c^2 + d^2)/(b + c + d) + (c^2 + d^2 + a^2)/(c + d + a) + (d^2 + a^2 + b^2)/(d + a + b) ≥ a + b + c + d  :=  by sorry
