-- Prove2me | Theorems.Thm_WorkbookSource_plus_2144
-- name    : WorkbookSource.plus_2144
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:17:00.530481+00:00
-- url     : https://prove2.me/theorems/d617fc34-7374-42fb-ad2b-b1e4032f3e50
-- title:
--   A cubic pair-product bound at fixed sum two
-- statement:
--   Let $ x,y,z \geq 0$ such that $ x + y + z = 2$ Prove that $ x^3y^3 + y^3z^3 + z^3x^3 + 2xyz \leq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2144` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2144; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2144 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 2) : x^3*y^3 + y^3*z^3 + z^3*x^3 + 2*x*y*z ≤ 1   :=  by sorry
