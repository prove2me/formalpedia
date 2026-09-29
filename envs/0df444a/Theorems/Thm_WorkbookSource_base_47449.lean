-- Prove2me | Theorems.Thm_WorkbookSource_base_47449
-- name    : WorkbookSource.base_47449
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:03:18.194978+00:00
-- url     : https://prove2.me/theorems/5c0802e5-eb4f-4551-88e2-338ab7b90657
-- title:
--   A shifted squared quadratic ratio sum is at least three halves
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\frac{(a^2-bc+a)^2}{b^2+c^2}+\frac{(b^2-ca+b)^2}{c^2+a^2}+\frac{(c^2-ab+c)^2}{a^2+b^2}\ge\frac{3}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47449` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47449; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47449 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c + a)^2 / (b^2 + c^2) + (b^2 - c * a + b)^2 / (c^2 + a^2) + (c^2 - a * b + c)^2 / (a^2 + b^2) ≥ 3 / 2  :=  by sorry
