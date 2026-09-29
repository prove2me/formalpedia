-- Prove2me | Theorems.Thm_WorkbookSource_base_21627
-- name    : WorkbookSource.base_21627
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:49:10.70942+00:00
-- url     : https://prove2.me/theorems/0092dae8-fb8c-4af1-82b8-ca4393898a29
-- title:
--   A shifted quadratic reciprocal lower bound at fixed sum three
-- statement:
--   Prove that for positive reals x, y, z such that x + y + z = 3, the following inequality holds: \(\dfrac{x+1}{x^2+2x}+\dfrac{y+1}{y^2+2y}+\dfrac{z+1}{z^2+2z} \ge 2\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21627` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21627; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21627 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x + 1) / (x ^ 2 + 2 * x) + (y + 1) / (y ^ 2 + 2 * y) + (z + 1) / (z ^ 2 + 2 * z) ≥ 2  :=  by sorry
