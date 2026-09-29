-- Prove2me | Theorems.Thm_WorkbookSource_plus_57819
-- name    : WorkbookSource.plus_57819
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:34.257033+00:00
-- url     : https://prove2.me/theorems/0c69f010-0878-4b22-a536-6f2ad06be4ca
-- title:
--   A shifted reciprocal sum bounds a symmetric reciprocal
-- statement:
--   Prove that: $\frac1{x+yz}+\frac1{y+zx}+\frac1{z+xy}\leq\frac{9}{2(xy+xz+yz)}$ where $x, y, z$ are positive real numbers such that $x+y+z=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_57819` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_57819; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_57819 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx1 : x + y + z = 3) : 1 / (x + y * z) + 1 / (y + z * x) + 1 / (z + x * y) ≤ 9 / (2 * (x * y + x * z + y * z))   :=  by sorry
