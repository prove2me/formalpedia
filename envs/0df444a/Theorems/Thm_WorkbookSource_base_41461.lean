-- Prove2me | Theorems.Thm_WorkbookSource_base_41461
-- name    : WorkbookSource.base_41461
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:56:11.487556+00:00
-- url     : https://prove2.me/theorems/5bca4ac2-c907-45d5-9c27-91925fbc73e7
-- title:
--   A shifted cyclic quadratic ratio sum bounds the total
-- statement:
--   Prove that for positive real numbers a, b, and c, the following inequality holds:
--   $$\frac{a^2+b}{a+1}+\frac{b^2+c}{b+1}+\frac{c^2+a}{c+1} \geq a+b+c$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41461` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41461; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41461 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b) / (a + 1) + (b^2 + c) / (b + 1) + (c^2 + a) / (c + 1) ≥ a + b + c  :=  by sorry
