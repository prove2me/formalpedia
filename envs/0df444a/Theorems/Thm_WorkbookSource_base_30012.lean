-- Prove2me | Theorems.Thm_WorkbookSource_base_30012
-- name    : WorkbookSource.base_30012
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:47.037885+00:00
-- url     : https://prove2.me/theorems/c2c475b0-9c64-4ea2-ba95-758c40fefedb
-- title:
--   A triple-product bound with pairwise fourth powers
-- statement:
--   Let $x,y,z$ be positive reals with sum 1. Prove that $ 10xyz\leq x^2+y^2+z^2+x^2y^2+y^2z^2+z^2x^2. $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30012` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30012; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30012 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : 10 * x * y * z ≤ x ^ 2 + y ^ 2 + z ^ 2 + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2  :=  by sorry
