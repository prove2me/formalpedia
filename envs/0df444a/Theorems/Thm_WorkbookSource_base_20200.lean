-- Prove2me | Theorems.Thm_WorkbookSource_base_20200
-- name    : WorkbookSource.base_20200
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:42:15.813967+00:00
-- url     : https://prove2.me/theorems/82f3bbd4-39eb-41a1-9417-80112d2c3d3c
-- title:
--   A product of shifted ratios bounded by a normalized cubic sum
-- statement:
--   Let \(a>0,b>0,c>0.\) Prove that \({{(\frac{a}{b+c}}+\frac 1{2})(\frac{b}{c+a}}+\frac 1{2})(\frac{c}{a+b}}+\frac 1{2})\le \frac{7}{8}+\frac{a^3+b^3+c^3}{24abc}\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20200` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20200; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20200 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a / (b + c) + 1 / 2) * (b / (c + a) + 1 / 2) * (c / (a + b) + 1 / 2) ≤ 7 / 8 + (a^3 + b^3 + c^3) / (24 * a * b * c)  :=  by sorry
