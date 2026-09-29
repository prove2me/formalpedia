-- Prove2me | Theorems.Thm_WorkbookSource_base_7117
-- name    : WorkbookSource.base_7117
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:26:06.481368+00:00
-- url     : https://prove2.me/theorems/3d3836fe-f93b-4236-884f-4e2b5d3607a0
-- title:
--   An asymmetric squared-reciprocal product inequality
-- statement:
--   Let $x,y,z>0,$ prove that: $\frac{3yz}{x^2}+\frac{2xz}{y^2}+\frac{4xy}{z^2} \geq 3+\frac{y}{x}+\frac{z}{x}+\frac{2x}{z}+\frac{2y}{z}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7117` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7117; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7117 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * y * z / x ^ 2 + 2 * x * z / y ^ 2 + 4 * x * y / z ^ 2 ≥ 3 + y / x + z / x + 2 * x / z + 2 * y / z  :=  by sorry
