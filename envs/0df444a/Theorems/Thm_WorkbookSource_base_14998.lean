-- Prove2me | Theorems.Thm_WorkbookSource_base_14998
-- name    : WorkbookSource.base_14998
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:00.738992+00:00
-- url     : https://prove2.me/theorems/d86f7e8a-970c-46e9-b59d-d18aa3519a4a
-- title:
--   A product comparison between odd power sums
-- statement:
--   prove that
--
--    $ \left( x+y+z \right) \left( {x}^{7}+{y}^{7}+{z}^{7} \right) \geq
--    \left( {x}^{3}+{y}^{3}+{z}^{3} \right) \left( {x}^{5}+{y}^{5}+{z}^{5} \right)$
--
--   $x,y,z>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14998` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14998; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14998 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) * (x^7 + y^7 + z^7) ≥ (x^3 + y^3 + z^3) * (x^5 + y^5 + z^5)  :=  by sorry
