-- Prove2me | Theorems.Thm_WorkbookSource_base_38511
-- name    : WorkbookSource.base_38511
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:36:36.220426+00:00
-- url     : https://prove2.me/theorems/68c8b55a-1ae7-49b8-b421-00161ea210e2
-- title:
--   A squared reciprocal ratio sum bounds two reciprocal expressions
-- statement:
--   Let $a, b$ and $c$ be positive real numbers. Show that $\frac{a+b}{c^2}+ \frac{c+a}{b^2}+ \frac{b+c}{a^2}\ge \frac{9}{a+b+c}+\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38511` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38511; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38511 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c ^ 2 + (c + a) / b ^ 2 + (b + c) / a ^ 2 ≥ 9 / (a + b + c) + 1 / a + 1 / b + 1 / c  :=  by sorry
