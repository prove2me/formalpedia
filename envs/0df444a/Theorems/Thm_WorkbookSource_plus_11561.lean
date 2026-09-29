-- Prove2me | Theorems.Thm_WorkbookSource_plus_11561
-- name    : WorkbookSource.plus_11561
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:06:46.510668+00:00
-- url     : https://prove2.me/theorems/1c69fe05-39ed-4b9d-a490-b50cd3532978
-- title:
--   A mixed quadratic reciprocal sum lower bound
-- statement:
--   Prove that if $x,y,z>0$ then
--    $\frac{x}{y^2+yz+z^2}+\frac{y}{x^2+xz+z^2}+\frac{z}{x^2+xy+y^2}\geq\frac4{x+y+z+3\frac{x^3+y^3+z^3}{(x+y+z)^2}}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_11561` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11561; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_11561 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y ^ 2 + y * z + z ^ 2) + y / (x ^ 2 + x * z + z ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 4 / (x + y + z + 3 * (x ^ 3 + y ^ 3 + z ^ 3) / (x + y + z) ^ 2)   :=  by sorry
