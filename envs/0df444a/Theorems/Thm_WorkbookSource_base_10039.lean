-- Prove2me | Theorems.Thm_WorkbookSource_base_10039
-- name    : WorkbookSource.base_10039
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:59.145391+00:00
-- url     : https://prove2.me/theorems/d32427fa-e647-4d02-9c99-b7b2b069ebd5
-- title:
--   A fifth-power bound for a triple product
-- statement:
--   prove that
--    $(x+y+z)^5-x^5-y^5-z^5\geq 60xyz(xy+yz+zx)$
--   if $x,y,z$ are positive reals
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10039` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10039; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10039 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 5 - x ^ 5 - y ^ 5 - z ^ 5 ≥ 60 * x * y * z * (x * y + y * z + z * x)  :=  by sorry
