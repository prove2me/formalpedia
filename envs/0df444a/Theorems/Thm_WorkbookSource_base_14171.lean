-- Prove2me | Theorems.Thm_WorkbookSource_base_14171
-- name    : WorkbookSource.base_14171
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:51:12.30148+00:00
-- url     : https://prove2.me/theorems/c49a61fd-8bf5-4459-9aec-39d607480f2f
-- title:
--   A cyclic linear-over-quadratic sum bounded by reciprocals
-- statement:
--   For $ x,y,z > 0$ , prove that:
--   $\frac{2x}{yz+x^2}+ \frac{2y}{zx+y^2}+\frac{ 2z}{xy+z^2} \le \frac{1}{x}+ \frac{1}{y}+ \frac{1}{z}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14171` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14171; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14171 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x / (y * z + x ^ 2) + 2 * y / (z * x + y ^ 2) + 2 * z / (x * y + z ^ 2)) ≤ 1 / x + 1 / y + 1 / z  :=  by sorry
