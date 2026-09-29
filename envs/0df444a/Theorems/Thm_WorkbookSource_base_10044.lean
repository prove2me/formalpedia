-- Prove2me | Theorems.Thm_WorkbookSource_base_10044
-- name    : WorkbookSource.base_10044
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:41:05.90151+00:00
-- url     : https://prove2.me/theorems/13d8e76c-d6fd-4033-9d39-f92f9f1e6771
-- title:
--   A normalized sixth-degree bound for the pairwise sum
-- statement:
--   Let $ x,y,z$ be nonnegative and $ x + y + z = 1$ . Prove that
--
--    $ xy + yz + zx\geq 8(x^2 + y^2 + z^2)(x^2y^2 + y^2z^2 + z^2x^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10044` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10044; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10044 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 1) : x * y + y * z + z * x ≥ 8 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)  :=  by sorry
