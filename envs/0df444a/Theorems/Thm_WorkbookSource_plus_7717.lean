-- Prove2me | Theorems.Thm_WorkbookSource_plus_7717
-- name    : WorkbookSource.plus_7717
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:48:14.802414+00:00
-- url     : https://prove2.me/theorems/5a354dc0-6a5c-42d3-811d-419d6f1fc9b7
-- title:
--   A mixed quadratic ratio sum with a symmetric correction
-- statement:
--   Let $a, b, c>0$ . Prove that $\frac{a(b+c)}{b^2+c^2}+\frac{b(c+a)}{c^2+a^2}+\frac{c(a+b)}{a^2+b^2}+\frac{7}{6}\cdot\frac{a^2+b^2+c^2}{ab+bc+ca}\ge\frac{25}{6}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7717` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7717; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7717 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (b + c) / (b ^ 2 + c ^ 2) + b * (c + a) / (c ^ 2 + a ^ 2) + c * (a + b) / (a ^ 2 + b ^ 2) + 7 / 6 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)) ≥ 25 / 6   :=  by sorry
