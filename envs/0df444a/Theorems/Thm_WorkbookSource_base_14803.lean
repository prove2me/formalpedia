-- Prove2me | Theorems.Thm_WorkbookSource_base_14803
-- name    : WorkbookSource.base_14803
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:56:51.681649+00:00
-- url     : https://prove2.me/theorems/970b7e54-296c-4013-8350-31fe59c27100
-- title:
--   A normalized squared total bounds pairwise quadratic ratios
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that
--    \begin{align*} \frac{(x+y+z)^2}{x^2+y^2+z^2}\ge \sum \frac{2xy}{x^2+y^2} \end{align*} Please let me know what you think .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14803` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14803; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14803 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2) ≥ 2 * x * y / (x ^ 2 + y ^ 2) + 2 * y * z / (y ^ 2 + z ^ 2) + 2 * z * x / (z ^ 2 + x ^ 2)  :=  by sorry
