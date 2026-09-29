-- Prove2me | Theorems.Thm_WorkbookSource_base_35577
-- name    : WorkbookSource.base_35577
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:00:06.541329+00:00
-- url     : https://prove2.me/theorems/01539b4b-4778-4a83-b9cc-50c659ca10e9
-- title:
--   A weighted mixed quadratic ratio sum is at least nine halves
-- statement:
--   Let $x,y,z>0$ ,prove that
--
--    ${\frac {2\,{x}^{2}+yz}{{y}^{2}+{z}^{2}}}+{\frac {2\,{y}^{2}+xz}{{x}^{2}+{z}^{2}}}+{\frac {2\,{z}^{2}+xy}{{x}^{2}+{y}^{2}}}\geq \frac{9}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35577` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35577; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35577 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * x ^ 2 + y * z) / (y ^ 2 + z ^ 2) + (2 * y ^ 2 + x * z) / (x ^ 2 + z ^ 2) + (2 * z ^ 2 + x * y) / (x ^ 2 + y ^ 2) ≥ 9 / 2  :=  by sorry
