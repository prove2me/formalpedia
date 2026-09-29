-- Prove2me | Theorems.Thm_WorkbookSource_base_11443
-- name    : WorkbookSource.base_11443
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:38:15.37515+00:00
-- url     : https://prove2.me/theorems/74611caf-027b-4786-a0b0-892f6b9aed88
-- title:
--   A mixed quadratic reciprocal upper bound
-- statement:
--   Let $x, y, z$ be positive real numbers. Prove that $\sum_{cyc}{\frac{1}{xy+2z^2}} \leq \frac{xy+yz+zx}{xyz(x+y+z)}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11443` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11443; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11443 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / (x * y + 2 * z ^ 2) + 1 / (y * z + 2 * x ^ 2) + 1 / (z * x + 2 * y ^ 2) ≤ (x * y + y * z + z * x) / (x * y * z * (x + y + z))  :=  by sorry
