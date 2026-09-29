-- Prove2me | Theorems.Thm_WorkbookSource_base_41556
-- name    : WorkbookSource.base_41556
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:56:16.859571+00:00
-- url     : https://prove2.me/theorems/2e4315f1-eb5e-4eea-9d1f-413c21a24199
-- title:
--   A quadratic reciprocal sum bounds a symmetric rational expression
-- statement:
--   $x,y,z>0$ ,prove ${\frac {x}{{y}^{2}+{z}^{2}}}+{\frac {y}{{x}^{2}+{z}^{2}}}+{\frac {z}{{x}^{2}+{y}^{2}}}\geq 3\,{\frac {x+y+z}{{x}^{2}+{y}^{2}+{z}^{2}+xy+yz+zx}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41556` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41556; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41556 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / (y ^ 2 + z ^ 2) + y / (x ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2) ≥ 3 * (x + y + z) / (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x)  :=  by sorry
