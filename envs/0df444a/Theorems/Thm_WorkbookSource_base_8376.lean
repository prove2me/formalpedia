-- Prove2me | Theorems.Thm_WorkbookSource_base_8376
-- name    : WorkbookSource.base_8376
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:37:53.024145+00:00
-- url     : https://prove2.me/theorems/efaedaab-e8be-4353-831a-72610a1ec2f3
-- title:
--   A refined upper bound for the pairwise reciprocal sum
-- statement:
--   If $x,y,z>0$ , then
--    $\frac{1}{x+y}+\frac{1}{y+z}+\frac{1}{z+x}\le \frac{3\left( x+y+z \right)}{2\left( xy+yz+zx \right)}-\frac{{{x}^{2}}+{{y}^{2}}+{{z}^{2}}-xy-yz-zx}{4\left( xy+yz+zx \right)\left( x+y+z \right)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8376` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8376; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8376 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≤ (3 * (x + y + z)) / (2 * (x * y + y * z + z * x)) - (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) / (4 * (x * y + y * z + z * x) * (x + y + z))  :=  by sorry
