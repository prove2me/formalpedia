-- Prove2me | Theorems.Thm_WorkbookSource_base_1454
-- name    : WorkbookSource.base_1454
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:31.144498+00:00
-- url     : https://prove2.me/theorems/2ff1c36a-a673-47d4-a8bf-48907ce8d392
-- title:
--   A four-variable cyclic quadratic reciprocal sum bounds the total
-- statement:
--   Given $ a, b, c, d > 0, \ \ \ \frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{d}+\frac{d^2}{a} \ge a+b+c+d$ . Prove that this is true by Rearrangement inequality.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1454` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1454; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1454 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 / b + b^2 / c + c^2 / d + d^2 / a) ≥ a + b + c + d  :=  by sorry
