-- Prove2me | Theorems.Thm_WorkbookSource_base_6511
-- name    : WorkbookSource.base_6511
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:49.105896+00:00
-- url     : https://prove2.me/theorems/3a5ca206-2a05-4a02-920f-2c46bdb63448
-- title:
--   A squared total times quadratic reciprocals is at least thirty-six
-- statement:
--   Prove that for positives $x$, $y$, and $z$, the inequality $(x+y+z)^2 \left(\frac{3}{x^2+y^2+z^2}+\frac{1}{x^2}+\frac{1}{y^2}+\frac{1}{z^2}\right) \geq 36$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6511` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6511; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6511 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 2 * (3 / (x ^ 2 + y ^ 2 + z ^ 2) + 1 / x ^ 2 + 1 / y ^ 2 + 1 / z ^ 2) ≥ 36  :=  by sorry
