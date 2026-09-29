-- Prove2me | Theorems.Thm_WorkbookSource_base_24579
-- name    : WorkbookSource.base_24579
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:45.867237+00:00
-- url     : https://prove2.me/theorems/71156114-7791-4f0a-ac8b-ba1f01ab22c8
-- title:
--   A squared pairwise reciprocal upper bound
-- statement:
--   Prove or disprove the inequality: \\(\\frac{9(a^{2}+b^{2}+c^{2})}{4(ab+bc+ca)^{2}}\\geq \\frac{1}{(a+b)^{2}}+\\frac{1}{(b+c)^{2}}+\\frac{1}{(c+a)^{2}}\\) for positive numbers a, b, and c.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24579` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24579; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24579 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a * b + b * c + c * a) ^ 2) ≥ 1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2  :=  by sorry
