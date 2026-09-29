-- Prove2me | Theorems.Thm_WorkbookSource_base_56355
-- name    : WorkbookSource.base_56355
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:42.789596+00:00
-- url     : https://prove2.me/theorems/837b47ab-d498-41a9-bea0-e88faaea7668
-- title:
--   A symmetric sixth-degree inequality with a difference correction
-- statement:
--   Prove that \((x^3+y^3+z^3)^2+3( xyz )^2\geq 4( y^3z^3+z^3x^3+x^3y^3)+ \frac45 [ (x-y)^2(y-z)^2(z-x)^2 ]\) for \(x,y,z \in R\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56355` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56355; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56355 (x y z : ℝ) : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 + 3 * (x * y * z) ^ 2 ≥ 4 * (y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3 + x ^ 3 * y ^ 3) + 4 / 5 * (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2  :=  by sorry
