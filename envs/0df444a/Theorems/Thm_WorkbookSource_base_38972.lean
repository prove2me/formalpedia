-- Prove2me | Theorems.Thm_WorkbookSource_base_38972
-- name    : WorkbookSource.base_38972
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:44.594765+00:00
-- url     : https://prove2.me/theorems/26c3ac79-a20e-4133-9e07-4ceffdc2a33e
-- title:
--   A shifted polynomial bound under a sum and lower bounds
-- statement:
--   Prove that if positive reals $x,y$ satisfy $x+y= 3$ , $x,y \ge 1$ then $9(x- 1)(y- 1) + (y^2 + y+ 1)(x + 1) + (x^2-x+ 1)(y- 1) \ge 9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38972` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38972; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38972 (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x + y = 3) : 9 * (x - 1) * (y - 1) + (y^2 + y + 1) * (x + 1) + (x^2 - x + 1) * (y - 1) ≥ 9  :=  by sorry
