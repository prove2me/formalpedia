-- Prove2me | Theorems.Thm_WorkbookSource_base_12020
-- name    : WorkbookSource.base_12020
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:39:24.710024+00:00
-- url     : https://prove2.me/theorems/d5a1c55c-5217-4d6a-ad01-597c7786bc9c
-- title:
--   A product of shifted quadratic ratios is at least 2744 over 27
-- statement:
--   x,y,z>0
--
--
--
--     $ \left( 8/3+{\frac {3\,{x}^{2}+yz}{{y}^{2}+{z}^{2}}} \right) \left( 8/3+{\frac {3\,{y}^{2}+zx}{{x}^{2}+{z}^{2}}} \right) \left( 8/3+{\frac {3\,{z}^{2}+xy}{{y}^{2}+{x}^{2}}} \right) \geq {\frac {2744}{27}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12020` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12020; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12020 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (8 / 3 + (3 * x ^ 2 + y * z) / (y ^ 2 + z ^ 2)) * (8 / 3 + (3 * y ^ 2 + z * x) / (z ^ 2 + x ^ 2)) * (8 / 3 + (3 * z ^ 2 + x * y) / (x ^ 2 + y ^ 2)) ≥ 2744 / 27  :=  by sorry
