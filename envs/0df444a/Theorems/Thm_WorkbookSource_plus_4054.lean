-- Prove2me | Theorems.Thm_WorkbookSource_plus_4054
-- name    : WorkbookSource.plus_4054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:02:53.908085+00:00
-- url     : https://prove2.me/theorems/378d4f5d-3a97-4a57-b40c-5c6293ba657a
-- title:
--   A pairwise squared reciprocal product sum upper bound
-- statement:
--   Suppose that $x,y,z$ are positive real numbers. Prove that $\frac{1}{(x+y)^2(y+z)^2}+\frac{1}{(y+z)^2(z+x)^2}+\frac{1}{(z+x)^2(x+y)^2} \leq \frac{9}{16xyz(x+y+z)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_4054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_4054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_4054 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) ^ 2 * 1 / (y + z) ^ 2 + 1 / (y + z) ^ 2 * 1 / (z + x) ^ 2 + 1 / (z + x) ^ 2 * 1 / (x + y) ^ 2) ≤ 9 / (16 * x * y * z * (x + y + z))   :=  by sorry
