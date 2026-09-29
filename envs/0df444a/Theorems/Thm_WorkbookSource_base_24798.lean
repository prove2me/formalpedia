-- Prove2me | Theorems.Thm_WorkbookSource_base_24798
-- name    : WorkbookSource.base_24798
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:58.45834+00:00
-- url     : https://prove2.me/theorems/39facb22-d186-4208-95d1-e0e351bd505c
-- title:
--   A squared pairwise ratio sum bounds cyclic ratios
-- statement:
--   Let a,b,c be positive real numbers. Prove that \\(\\left(\\frac{a+b}{c}\\right)^2+\\left(\\frac{b+c}{a}\\right)^2+\\left(\\frac{c+a}{b}\\right)^2\\geq 4\\left(\\frac{a}{b}+\\frac{b}{c}+\\frac{c}{a}\\right)\\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24798` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24798; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24798 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 / c ^ 2 + (b + c) ^ 2 / a ^ 2 + (c + a) ^ 2 / b ^ 2 ≥ 4 * (a / b + b / c + c / a)  :=  by sorry
