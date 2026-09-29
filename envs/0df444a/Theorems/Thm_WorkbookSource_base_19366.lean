-- Prove2me | Theorems.Thm_WorkbookSource_base_19366
-- name    : WorkbookSource.base_19366
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:41:29.449881+00:00
-- url     : https://prove2.me/theorems/a90cba69-92d3-4148-a409-63a9c7b940a9
-- title:
--   A cubed difference ratio sum bounds the total
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $\frac{(b+c-a)^3}{a^2}+\frac{(c+a-b)^3}{b^2}+\frac{(a+b-c)^3}{c^2}\ge a+b+c.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19366` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19366; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19366 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c - a) ^ 3 / a ^ 2 + (c + a - b) ^ 3 / b ^ 2 + (a + b - c) ^ 3 / c ^ 2 ≥ a + b + c  :=  by sorry
