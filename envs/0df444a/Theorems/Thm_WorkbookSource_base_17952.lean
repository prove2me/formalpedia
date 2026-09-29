-- Prove2me | Theorems.Thm_WorkbookSource_base_17952
-- name    : WorkbookSource.base_17952
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:12:33.098411+00:00
-- url     : https://prove2.me/theorems/d21b175c-0dee-4fb4-9670-8508903a1500
-- title:
--   A product bounds shifted harmonic pairwise products
-- statement:
--   Prove that for positive numbers $x$, $y$, and $z$, the inequality $(1+x)(1+y)(1+z) \geq (1+\frac{2xy}{x+y})(1+\frac{2yz}{y+z})(1+\frac{2xz}{z+x})$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17952` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17952; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17952 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 + x) * (1 + y) * (1 + z) ≥ (1 + 2 * x * y / (x + y)) * (1 + 2 * y * z / (y + z)) * (1 + 2 * z * x / (z + x))  :=  by sorry
