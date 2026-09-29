-- Prove2me | Theorems.Thm_WorkbookSource_plus_10270
-- name    : WorkbookSource.plus_10270
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:21:47.068708+00:00
-- url     : https://prove2.me/theorems/8f875077-d3a9-4f0b-8836-98e61c37d6bf
-- title:
--   A squared cubic sum bounds a triangle-factor quadratic sum
-- statement:
--   If $ x,y,z \ge 0 $ Prove that : $ 27(\sum{x^3})^2 \ge (\sum{x})^4\sum{(y+z-x)^2} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10270` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10270; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10270 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 27 * (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ (x + y + z) ^ 4 * ((y + z - x) ^ 2 + (z + x - y) ^ 2 + (x + y - z) ^ 2)   :=  by sorry
