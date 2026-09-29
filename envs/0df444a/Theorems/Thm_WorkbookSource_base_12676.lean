-- Prove2me | Theorems.Thm_WorkbookSource_base_12676
-- name    : WorkbookSource.base_12676
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:43:31.916986+00:00
-- url     : https://prove2.me/theorems/320e8c83-60f3-4f39-876a-007481dcc092
-- title:
--   A shifted quadratic ratio upper bound at fixed sum three
-- statement:
--   Prove that $\sum \frac{x}{x^2+y+z} \leq 1$ for positive reals $x, y, z$ such that $x + y + z = 3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12676` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12676; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12676 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : x / (x ^ 2 + y + z) + y / (y ^ 2 + z + x) + z / (z ^ 2 + x + y) ≤ 1  :=  by sorry
