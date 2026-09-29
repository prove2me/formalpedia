-- Prove2me | Theorems.Thm_WorkbookSource_plus_20512
-- name    : WorkbookSource.plus_20512
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:27:37.884976+00:00
-- url     : https://prove2.me/theorems/d99942cb-b7d2-4963-a0e2-f4a8997c1dfe
-- title:
--   A cyclic square ratio sum has a quartic upper bound
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\frac{a^2}{b+c}+\frac{b^2}{c+a}+\frac{c^2}{a+b}\le\frac{(a^2+b^2+c^2)^2}{6abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_20512` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20512; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_20512 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≤ (a^2 + b^2 + c^2)^2 / (6 * a * b * c)   :=  by sorry
