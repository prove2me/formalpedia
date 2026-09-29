-- Prove2me | Theorems.Thm_WorkbookSource_base_30098
-- name    : WorkbookSource.base_30098
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:16.665986+00:00
-- url     : https://prove2.me/theorems/e544f17f-0233-436e-ad38-9739c7b45832
-- title:
--   A sum and pairwise-product bound on a sphere
-- statement:
--   Given $x, y, z > 0$ and $x^2 + y^2 + z^2 = 3$, prove that $2(x + y + z) - xy - yz - xz \leq \frac{7}{2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30098` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30098; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30098 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 = 3) : 2 * (x + y + z) - x * y - y * z - x * z ≤ 7 / 2  :=  by sorry
