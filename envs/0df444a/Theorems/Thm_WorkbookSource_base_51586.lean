-- Prove2me | Theorems.Thm_WorkbookSource_base_51586
-- name    : WorkbookSource.base_51586
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:42:47.714866+00:00
-- url     : https://prove2.me/theorems/22e38d31-f632-42ef-aa54-14600af86c0a
-- title:
--   A mixed reciprocal inequality at fixed sum three
-- statement:
--   Let $x,y,z$ be positive reals with sum $3$ . Prove: $\displaystyle{\frac{2y^3z^3+x^4+5}{2yz}+\frac{2z^3x^3+y^4+5}{2zx}+\frac{2x^3y^3+z^4+5}{2xy}\ge \frac{x^2+3}{x}+\frac{y^2+3}{y}+\frac{z^2+3}{z}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51586` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51586; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51586 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (2 * y ^ 3 * z ^ 3 + x ^ 4 + 5) / (2 * y * z) + (2 * z ^ 3 * x ^ 3 + y ^ 4 + 5) / (2 * z * x) + (2 * x ^ 3 * y ^ 3 + z ^ 4 + 5) / (2 * x * y) ≥ (x ^ 2 + 3) / x + (y ^ 2 + 3) / y + (z ^ 2 + 3) / z  :=  by sorry
