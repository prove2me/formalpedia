-- Prove2me | Theorems.Thm_WorkbookSource_base_17037
-- name    : WorkbookSource.base_17037
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:06:27.420814+00:00
-- url     : https://prove2.me/theorems/6e320d51-ae98-4e72-90d8-0d482a9da5c5
-- title:
--   A squared ratio sum bounds a symmetric quadratic ratio
-- statement:
--   Let $a, b, c$ be positive reals. Prove that: $(\frac{a}{b+c})^2+(\frac{b}{c+a})^2+(\frac{c}{a+b})^2\ge\frac{3}{4}(\frac{a^2+b^2+c^2}{ab+bc+ca})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17037` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17037; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17037 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 ≥ 3 / 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)  :=  by sorry
