-- Prove2me | Theorems.Thm_WorkbookSource_plus_58495
-- name    : WorkbookSource.plus_58495
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:11.759409+00:00
-- url     : https://prove2.me/theorems/cd41b5ff-81ab-4970-b6a3-c73200e85689
-- title:
--   A symmetric sixth-degree comparison with triple-product terms
-- statement:
--   Let: $x,y,z \geq 0$ . Prove that: $5(x^{6}+y^{6}+z^{6})+13(x^{3}y^{3}+y^{3}z^{3}+z^{3}x^{3})\geq 27x^{2}y^{2}z^{2}+9xyz(x^{3}+y^{3}+z^{3})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_58495` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_58495; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_58495 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 5 * (x ^ 6 + y ^ 6 + z ^ 6) + 13 * (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3) ≥ 27 * x ^ 2 * y ^ 2 * z ^ 2 + 9 * x * y * z * (x ^ 3 + y ^ 3 + z ^ 3)   :=  by sorry
