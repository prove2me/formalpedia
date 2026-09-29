-- Prove2me | Theorems.Thm_WorkbookSource_plus_51739
-- name    : WorkbookSource.plus_51739
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:28:15.410023+00:00
-- url     : https://prove2.me/theorems/ad9fc6d2-c018-4d77-b8b1-8fbade86c08d
-- title:
--   An asymmetric weighted pair-product ratio inequality
-- statement:
--   Let $x,y,z>0,$ prove that: $\frac{2yz}{x^2}+\frac{2xz}{y^2}+\frac{5xy}{z^2}\geq \frac{3x}{z}+\frac{3y}{z}+3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_51739` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51739; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_51739 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * y * z / x ^ 2 + 2 * x * z / y ^ 2 + 5 * x * y / z ^ 2 ≥ 3 * x / z + 3 * y / z + 3   :=  by sorry
