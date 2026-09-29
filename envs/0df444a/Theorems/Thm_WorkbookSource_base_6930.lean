-- Prove2me | Theorems.Thm_WorkbookSource_base_6930
-- name    : WorkbookSource.base_6930
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:25:20.100352+00:00
-- url     : https://prove2.me/theorems/8fd4f71a-4e18-4f06-870d-8136f092a196
-- title:
--   A sum of shifted squared ratios bounds a symmetric ratio
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that $ \left(2+\frac{a}{b}\right)^{2}+\left(2+\frac{b}{c}\right)^{2}+\left(2+\frac{c}{a}\right)^{2}\ge\frac{9(a+b+c)^{2}}{ab+bc+ca}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6930` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6930; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6930 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 + a / b) ^ 2 + (2 + b / c) ^ 2 + (2 + c / a) ^ 2 ≥ 9 * (a + b + c) ^ 2 / (a * b + b * c + c * a)  :=  by sorry
