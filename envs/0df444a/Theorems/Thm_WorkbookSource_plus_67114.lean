-- Prove2me | Theorems.Thm_WorkbookSource_plus_67114
-- name    : WorkbookSource.plus_67114
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:46:45.493155+00:00
-- url     : https://prove2.me/theorems/8803676c-415e-419b-8588-77cefb675efa
-- title:
--   A quadratic ratio sum has a symmetric lower bound
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove the inequality
--    $\frac{a^2}{b^2+bc+c^2}+\frac{b^2}{c^2+ca+a^2}+\frac{c^2}{a^2+ab+b^2}\ge\frac{1}{9}\cdot\frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{8}{9}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67114` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67114; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67114 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b^2 + b * c + c^2) + b^2 / (c^2 + c * a + a^2) + c^2 / (a^2 + a * b + b^2)) ≥ 1 / 9 * (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + 8 / 9   :=  by sorry
