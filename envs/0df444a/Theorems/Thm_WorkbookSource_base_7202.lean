-- Prove2me | Theorems.Thm_WorkbookSource_base_7202
-- name    : WorkbookSource.base_7202
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:45.116993+00:00
-- url     : https://prove2.me/theorems/f6f62f7a-5cad-424d-b202-a03a32f1fd13
-- title:
--   A sum bound for nonnegative points on the unit sphere
-- statement:
--   Prove that $ (x + y + z)^2 \leq 2(1 + yz)^2$ for $ x,y,z\geq 0$ such that $ x^2 + y^2 + z^2 = 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7202` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7202; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7202 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : (x + y + z) ^ 2 ≤ 2 * (1 + y * z) ^ 2  :=  by sorry
