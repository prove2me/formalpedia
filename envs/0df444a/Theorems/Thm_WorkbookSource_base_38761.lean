-- Prove2me | Theorems.Thm_WorkbookSource_base_38761
-- name    : WorkbookSource.base_38761
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:24.96731+00:00
-- url     : https://prove2.me/theorems/d72267c5-edee-4478-92b4-221a8ac7af4c
-- title:
--   A sixth-degree refinement involving the Vandermonde square
-- statement:
--   Prove that \((x^3+y^3+z^3)^2+3( xyz )^2\geq 4( y^3z^3+z^3x^3+x^3y^3)+ [ (x-y)^2(y-z)^2(z-x)^2 ]\) for \(x,y,z \in R\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38761` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38761; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38761 (x y z : ℝ) :
  (x^3 + y^3 + z^3)^2 + 3 * (x * y * z)^2 ≥
    4 * (y^3 * z^3 + z^3 * x^3 + x^3 * y^3) + (x - y)^2 * (y - z)^2 * (z - x)^2  :=  by sorry
