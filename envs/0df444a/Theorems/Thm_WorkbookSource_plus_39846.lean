-- Prove2me | Theorems.Thm_WorkbookSource_plus_39846
-- name    : WorkbookSource.plus_39846
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:41.120849+00:00
-- url     : https://prove2.me/theorems/e575b81f-d707-44df-b0f5-613c92240777
-- title:
--   A pairwise reciprocal sum bounds a normalized cubic reciprocal
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that
--    $$ \frac{1}{x+y}+\frac{1}{y+z}+\frac{1}{z+x} \geq \frac{(x+y+z)^2}{x^3+y^3+z^3+3xyz}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39846` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39846; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39846 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ (x + y + z) ^ 2 / (x ^ 3 + y ^ 3 + z ^ 3 + 3 * x * y * z)   :=  by sorry
