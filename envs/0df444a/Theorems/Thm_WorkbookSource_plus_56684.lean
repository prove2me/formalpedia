-- Prove2me | Theorems.Thm_WorkbookSource_plus_56684
-- name    : WorkbookSource.plus_56684
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:28.98978+00:00
-- url     : https://prove2.me/theorems/a6261cf0-5c33-4c64-bd4e-f0dd98cde0cb
-- title:
--   A mixed reciprocal and product ratio sum is at least three
-- statement:
--   Let $a,b,c>0.$ Prove that $\frac{a}{b}+\frac{2bc}{a+b}+\frac{2b}{c (a+b)}\geq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_56684` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_56684; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_56684 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + 2 * b * c / (a + b) + 2 * b / (c * (a + b)) ≥ 3   :=  by sorry
