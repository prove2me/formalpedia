-- Prove2me | Theorems.Thm_WorkbookSource_base_18343
-- name    : WorkbookSource.base_18343
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:32:45.758432+00:00
-- url     : https://prove2.me/theorems/403497ab-5a9d-46b7-8145-e13b5cce37d2
-- title:
--   A quadratic reciprocal lower bound involving pairwise products
-- statement:
--   If $x, y, z$ are positive real numbers, then prove that $\frac{1}{x^{2}+y^{2}}+\frac{1}{y^{2}+z^{2}}+\frac{1}{z^{2}+x^{2}}\ge \frac{5}{2(xy+yz+zx)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18343` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18343; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18343 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2) ≥ 5 / (2 * (x * y + y * z + z * x))  :=  by sorry
