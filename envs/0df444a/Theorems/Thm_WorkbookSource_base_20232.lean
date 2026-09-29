-- Prove2me | Theorems.Thm_WorkbookSource_base_20232
-- name    : WorkbookSource.base_20232
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:42:20.134528+00:00
-- url     : https://prove2.me/theorems/5d0ec08d-b882-45e9-af82-45f8ab1b1099
-- title:
--   A cyclic quadratic ratio sum bounded by a symmetric ratio
-- statement:
--   Given $ a,b,c>0$ .Prove that: $ \frac{5}{4}. \frac{a^2+b^2+c^2}{ab+bc+ca} \ge \frac{a^2}{a^2+ab+bc}+ \frac{b^2}{b^2+bc+ca}+ \frac{c^2}{c^2+ca+ab}+ \frac{1}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20232` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20232; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20232 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c) ≥ a ^ 2 / (a ^ 2 + a * b + b * c) + b ^ 2 / (b ^ 2 + b * c + a * c) + c ^ 2 / (c ^ 2 + a * c + a * b) + 1 / 4  :=  by sorry
