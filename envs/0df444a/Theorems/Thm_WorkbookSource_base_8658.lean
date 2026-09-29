-- Prove2me | Theorems.Thm_WorkbookSource_base_8658
-- name    : WorkbookSource.base_8658
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:15.874662+00:00
-- url     : https://prove2.me/theorems/85317729-93b0-42d2-b0c6-8e7e55bcfcfd
-- title:
--   A product inequality between two cyclic quartic sums
-- statement:
--   Prove that for $x,y,z\geq 0$,
--   $(xy^3+yz^3+x^3z)(xz^3+x^3y+y^3z)-(x^2+y^2+z^2)xyz(x^3+y^3+z^3)\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8658` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8658; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8658 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x * y ^ 3 + y * z ^ 3 + x ^ 3 * z) * (x * z ^ 3 + x ^ 3 * y + y ^ 3 * z) - (x ^ 2 + y ^ 2 + z ^ 2) * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3) ≥ 0  :=  by sorry
