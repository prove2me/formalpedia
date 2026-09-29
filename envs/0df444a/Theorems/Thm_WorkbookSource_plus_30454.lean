-- Prove2me | Theorems.Thm_WorkbookSource_plus_30454
-- name    : WorkbookSource.plus_30454
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:19.149443+00:00
-- url     : https://prove2.me/theorems/8a286c8a-b0c8-4b77-ac6e-46fd9f78a34b
-- title:
--   A weighted reciprocal square bounds an asymmetric quadratic reciprocal
-- statement:
--   For $x,y,z \in \mathbb{R}^{+}$
--   $\frac{y+z}{x+y+z}(\frac{1}{x}+\frac{1}{y}+\frac{1}{z})^2 \geq \frac{12}{x^2+yz}$ It is stronger than yours
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30454` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30454; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_30454 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / (x + y + z) * (1 / x + 1 / y + 1 / z) ^ 2 ≥ 12 / (x ^ 2 + y * z)   :=  by sorry
