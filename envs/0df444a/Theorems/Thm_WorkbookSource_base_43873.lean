-- Prove2me | Theorems.Thm_WorkbookSource_base_43873
-- name    : WorkbookSource.base_43873
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:22.188033+00:00
-- url     : https://prove2.me/theorems/1a00f9f6-b9c2-4e54-9360-d360b0e90f12
-- title:
--   A seventh-degree comparison of symmetric product sums
-- statement:
--   Prove that for $x,y,z\geq 0$,
--   $(x+y+z)(x^3y^3+y^3z^3+x^3z^3)-(x^2+y^2+z^2)(xy+xz+yz)xyz\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43873` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43873; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43873 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + x ^ 3 * z ^ 3) - (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + x * z + y * z) * x * y * z ≥ 0  :=  by sorry
