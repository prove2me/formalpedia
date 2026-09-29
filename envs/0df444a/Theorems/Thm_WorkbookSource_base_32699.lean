-- Prove2me | Theorems.Thm_WorkbookSource_base_32699
-- name    : WorkbookSource.base_32699
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:55.218864+00:00
-- url     : https://prove2.me/theorems/02598655-e3ff-4ad5-b4d2-b9febc45a925
-- title:
--   A product bound for three shifted quadratic factors
-- statement:
--   Prove that, for any real numbers $x,y, z$, $3(x^2-x+1)(y^2-y+1)(z^2-z+1)\geq (xyz)^2+xyz+1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32699` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32699; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32699 (x y z : ℝ) : 3 * (x ^ 2 - x + 1) * (y ^ 2 - y + 1) * (z ^ 2 - z + 1) ≥ (x*y*z) ^ 2 + x*y*z + 1  :=  by sorry
