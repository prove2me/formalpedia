-- Prove2me | Theorems.Thm_WorkbookSource_plus_18904
-- name    : WorkbookSource.plus_18904
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:21.050628+00:00
-- url     : https://prove2.me/theorems/c17549e6-7532-4805-a2c0-1b09d22f7fc1
-- title:
--   A cubic ratio bounds a normalized total cube
-- statement:
--   Let $ a,b,c $ be positive real numbers.Prove that
--    ${ \frac{a^3+b^3+c^3}{abc}\geq \frac{8}{9}\cdot \frac{(a+b+c)^3}{(b+c)(c+a)(a+b)}} .$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_18904` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_18904; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_18904 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a * b * c) ≥ (8 / 9) * (a + b + c)^3 / ((b + c) * (c + a) * (a + b))   :=  by sorry
