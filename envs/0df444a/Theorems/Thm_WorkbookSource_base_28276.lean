-- Prove2me | Theorems.Thm_WorkbookSource_base_28276
-- name    : WorkbookSource.base_28276
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:17:59.089182+00:00
-- url     : https://prove2.me/theorems/bc747c39-0269-4241-b1e4-695f74ca9ce0
-- title:
--   A product comparison involving shifted squares and pairwise sums
-- statement:
--   If $a,b,c$ are real numbers, then
--
--    $\left(a^2+\frac 1{2}\right)\left(b^2+\frac 1{2}\right)\left(c^2+\frac 1{2}\right)\ge \left(a+b-\frac 1{2}\right)\left(b+c-\frac 1{2}\right)\left(c+a-\frac 1{2}\right).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28276` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28276; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28276 (a b c : ℝ) : (a^2 + 1/2) * (b^2 + 1/2) * (c^2 + 1/2) ≥ (a + b - 1/2) * (b + c - 1/2) * (c + a - 1/2)  :=  by sorry
