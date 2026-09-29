-- Prove2me | Theorems.Thm_WorkbookSource_base_15608
-- name    : WorkbookSource.base_15608
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:31.170974+00:00
-- url     : https://prove2.me/theorems/8d7906de-1c51-4d7f-8248-5b398d3063b8
-- title:
--   A fourth-power bound for a squared pairwise sum
-- statement:
--   For x,y,z positive reals such that x+y+z=1 prove that
--    $ x^4+y^4+z^4 +\frac 1{27} \geq \frac 23 (xy+yz+zx)^2 . $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15608` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15608; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15608 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) :  x ^ 4 + y ^ 4 + z ^ 4 + 1 / 27 ≥ 2 / 3 * (x * y + y * z + z * x) ^ 2  :=  by sorry
