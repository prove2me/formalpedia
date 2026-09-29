-- Prove2me | Theorems.Thm_WorkbookSource_problem_40872
-- name    : WorkbookSource.problem_40872
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:20.439653+00:00
-- url     : https://prove2.me/theorems/116ecf40-582f-4c0a-ac42-d4f14e20cddb
-- title:
--   A symmetric product lower bound
-- statement:
--   For positive real $x,y,z$,
--
--   $$(x^2+yz)(y+z)\ge4xyz.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40872` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40872; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40872 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y * z) * (y + z) ≥ 4 * x * y * z  :=  by sorry
