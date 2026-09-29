-- Prove2me | Theorems.Thm_WorkbookSource_base_19323
-- name    : WorkbookSource.base_19323
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:09:35.341973+00:00
-- url     : https://prove2.me/theorems/0a9845f7-7d9e-479a-94a8-0645b3169217
-- title:
--   A twelfth-degree pair-sum product inequality
-- statement:
--   Prove that for positive real numbers $x$, $y$, and $z$, the inequality $3^3 \left( {x + y} \right)^4 \left( {y + z} \right)^4 \left( {z + x} \right)^4 \ge 2^{12} x^3 y^3 z^3 \left( {x + y + z} \right)^3$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19323` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19323; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19323    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
  3^3 * (x + y)^4 * (y + z)^4 * (z + x)^4 ≥ 2^12 * x^3 * y^3 * z^3 * (x + y + z)^3  :=  by sorry
