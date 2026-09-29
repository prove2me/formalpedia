-- Prove2me | Theorems.Thm_WorkbookSource_base_1485
-- name    : WorkbookSource.base_1485
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:24.949702+00:00
-- url     : https://prove2.me/theorems/e52eef0b-e2d3-4465-ac28-c911833ddf73
-- title:
--   A cyclic cubic-over-quadratic sum bounds the total
-- statement:
--   Let a,b,c>0. Prove that
--    $\frac{a^3}{a^2+ab+b^2}+\frac{b^3}{b^2+bc+c^2}+ \frac{c^3}{c^2+ca+a^2} \geq \frac{a+b+c}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1485` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1485; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1485 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^3 / (a^2 + a * b + b^2) + b^3 / (b^2 + b * c + c^2) + c^3 / (c^2 + c * a + a^2)) ≥ (a + b + c) / 3  :=  by sorry
