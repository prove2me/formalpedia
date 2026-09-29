-- Prove2me | Theorems.Thm_WorkbookSource_base_57004
-- name    : WorkbookSource.base_57004
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:12.862138+00:00
-- url     : https://prove2.me/theorems/07a17b16-a667-4ea7-ab0c-d22d16ef6840
-- title:
--   A cyclic squared product ratio bounds half the cubic sum
-- statement:
--   Prove that, for every positive real numbers $ a,b,c$ , the following inequality always holds: $ \frac{a^2b^2}{a+b}+\frac{b^2c^2}{b+c}+\frac{c^2a^2}{c+a}\le\frac{a^3+b^3+c^3}2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57004` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57004; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_57004 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b^2 / (a + b) + b^2 * c^2 / (b + c) + c^2 * a^2 / (c + a)) ≤ (a^3 + b^3 + c^3) / 2  :=  by sorry
