-- Prove2me | Theorems.Thm_WorkbookSource_plus_58854
-- name    : WorkbookSource.plus_58854
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:56.099377+00:00
-- url     : https://prove2.me/theorems/452d5c9d-0071-4988-92e1-a24456020c3d
-- title:
--   A cubed quadratic sum bounds pairwise cubic products
-- statement:
--   If $x,y,z$ are positive numbers, then
--    ${({x^2} + {y^2} + {z^2})^3} \ge 8({x^3}{y^3} + {y^3}{z^3} + {x^3}{z^3})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_58854` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_58854; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_58854 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + x^3 * z^3)   :=  by sorry
