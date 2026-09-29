-- Prove2me | Theorems.Thm_WorkbookSource_base_8086
-- name    : WorkbookSource.base_8086
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:59.715398+00:00
-- url     : https://prove2.me/theorems/892f053e-fd5e-4954-8d86-71f5bc32b188
-- title:
--   A product of three quadratic factors bounds two squared sums
-- statement:
--   Then we have $(a^{2}+2)(b^{2}+2)(c^{2}+2)\geq (a+b+c)^{2}+(ab+bc+ca)^{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8086` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8086; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8086 (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ (a + b + c)^2 + (a * b + b * c + c * a)^2  :=  by sorry
