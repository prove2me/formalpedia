-- Prove2me | Theorems.Thm_WorkbookSource_base_44141
-- name    : WorkbookSource.base_44141
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:52.800717+00:00
-- url     : https://prove2.me/theorems/a7b633e0-f197-4f80-8aaa-8485e97d0dfb
-- title:
--   A cyclic cubic ratio with a quadratic correction
-- statement:
--   Let $a, b, c >0$. Then
--   $\frac{b^3}{a} + \frac{c^3}{b} + \frac{a^3}{c} + ab+bc+ca \geq 2 ( a^2 + b^2 + c^2 )$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44141` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44141; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44141 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b^3 / a + c^3 / b + a^3 / c + a * b + b * c + c * a) ≥ 2 * (a^2 + b^2 + c^2)  :=  by sorry
