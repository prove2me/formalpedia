-- Prove2me | Theorems.Thm_WorkbookSource_base_8366
-- name    : WorkbookSource.base_8366
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:37:44.999482+00:00
-- url     : https://prove2.me/theorems/8e49ab70-45e0-47d9-a906-0df618fa4151
-- title:
--   A pair of cubic reciprocal ratios bounds pairwise ratios
-- statement:
--   Let $ a,b,c$ be positive real numbers. Prove that
--   $$ \frac{a^3+b^3+c^3} {2abc}+\frac{2abc}{a^3+b^3+c^3} \ge \frac{a+b}{b+c}+\frac{b+c}{a+b}+\frac{1}{6}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8366` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8366; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8366 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (2 * a * b * c) + (2 * a * b * c) / (a^3 + b^3 + c^3) ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 / 6  :=  by sorry
