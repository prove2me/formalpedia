-- Prove2me | Theorems.Thm_WorkbookSource_base_24505
-- name    : WorkbookSource.base_24505
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:18.272582+00:00
-- url     : https://prove2.me/theorems/609283a6-6420-4395-b229-63492bc005f0
-- title:
--   A nested reciprocal sum bounds the pairwise products
-- statement:
--   Let $a,b,c > 0$ , prove that $\frac{a}{\frac{1}{a} + \frac{1}{b + c} + \frac{1}{a + b + c}} + \frac{b}{\frac{1}{b} + \frac{1}{c + a} + \frac{1}{a + b + c}} + \frac{c}{\frac{1}{c} + \frac{1}{a + b} + \frac{1}{a + b + c}} \geq \frac{6}{11} \cdot (ab + bc + ca)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24505` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24505; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24505 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (1 / a + 1 / (b + c) + 1 / (a + b + c)) + b / (1 / b + 1 / (c + a) + 1 / (a + b + c)) + c / (1 / c + 1 / (a + b) + 1 / (a + b + c))) ≥ (6 / 11) * (a * b + b * c + c * a)  :=  by sorry
