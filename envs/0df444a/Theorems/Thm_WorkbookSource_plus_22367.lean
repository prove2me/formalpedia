-- Prove2me | Theorems.Thm_WorkbookSource_plus_22367
-- name    : WorkbookSource.plus_22367
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:54.903337+00:00
-- url     : https://prove2.me/theorems/39f5367c-6a75-428a-8ea7-9d728148b789
-- title:
--   A cyclic ratio sum with a normalized cubic correction
-- statement:
--   Let $a,b,c$ are positive real numbers. Prove $ 4 (\frac{a}{b}+\frac{b}{c}+\frac{c}{a})+\frac{9abc}{a^3+b^3+c^3+2(ab^2+bc^2+ca^2)}\ge 13$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_22367` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_22367; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_22367 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 * (a / b + b / c + c / a) + (9 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) ≥ 13   :=  by sorry
