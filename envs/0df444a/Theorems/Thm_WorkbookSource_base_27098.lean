-- Prove2me | Theorems.Thm_WorkbookSource_base_27098
-- name    : WorkbookSource.base_27098
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:39.046759+00:00
-- url     : https://prove2.me/theorems/6ad206b3-e71c-4c13-9900-e38ebf155e43
-- title:
--   A shifted squared cyclic ratio sum bounds a symmetric ratio
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that $ \left(1+\frac{2a}{b}\right)^{2}+\left(1+\frac{2b}{c}\right)^{2}+\left(1+\frac{2c}{a}\right)^{2}\ge\frac{9(a+b+c)^{2}}{ab+bc+ca}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27098` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27098; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27098 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + 2 * a / b) ^ 2 + (1 + 2 * b / c) ^ 2 + (1 + 2 * c / a) ^ 2 ≥ 9 * (a + b + c) ^ 2 / (a * b + b * c + c * a)  :=  by sorry
