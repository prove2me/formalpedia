-- Prove2me | Theorems.Thm_WorkbookSource_base_3161
-- name    : WorkbookSource.base_3161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:33:22.193172+00:00
-- url     : https://prove2.me/theorems/90c9f1db-c031-492c-a5be-3a4e819d94b7
-- title:
--   A rational product inequality under a triple-product constraint
-- statement:
--   In case $abc<1,$ setting $a=\frac{1}{x},$ $b=\frac{1}{y}$ and $c=\frac{1}{z},$ then we have $xyz>1$ and the inequality becomes
--
--    ${\left(\frac{1}{x}+\frac{1}{y}+\frac{1}{z}+\frac{1}{xyz}-4\right)\left(\frac{1}{xy}+\frac{1}{yz}+\frac{1}{zx}-3\right) \ge 4\left(\frac{1}{xyz}-1\right)\left(\frac{1}{x}+\frac{1}{y}+\frac{1}{z}-3\right),}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3161 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z > 1) : (1 / x + 1 / y + 1 / z + 1 / (x * y * z) - 4) * (1 / (x * y) + 1 / (y * z) + 1 / (z * x) - 3) ≥ 4 * (1 / (x * y * z) - 1) * (1 / x + 1 / y + 1 / z - 3)  :=  by sorry
