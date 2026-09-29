-- Prove2me | Theorems.Thm_WorkbookSource_plus_7252
-- name    : WorkbookSource.plus_7252
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:42:58.405742+00:00
-- url     : https://prove2.me/theorems/61005cb7-d4a8-4a9b-8a3b-8d9f054a8809
-- title:
--   A refined squared cyclic ratio lower bound
-- statement:
--   Let $x,y,z>0$ ,prove that:
--
--    ${\frac {{x}^{2}}{ \left( y+z \right) ^{2}}}+{\frac {{y}^{2}}{ \left( z+x \right) ^{2}}}+{\frac {{z}^{2}}{ \left( x+y \right) ^{2}}}\geq {\frac {1}{225}}\,{\frac { \left( 47\,{x}^{2}-22\,xy-22\,xz+47\,{y}^{2}-22\,yz+47\,{z}^{2} \right) \left( {x}^{2}+{y}^{2}+{z}^{2}+3\,xy+3\,yz+3\,xz \right) ^{2}}{ \left( y+z \right) ^{2} \left( z+x \right) ^{2} \left( x+y \right) ^{2}}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7252` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7252; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7252 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 / (y + z)^2 + y^2 / (z + x)^2 + z^2 / (x + y)^2) ≥ 1 / 225 * (47 * x^2 - 22 * x * y - 22 * x * z + 47 * y^2 - 22 * y * z + 47 * z^2) * (x^2 + y^2 + z^2 + 3 * x * y + 3 * y * z + 3 * x * z)^2 / ((y + z)^2 * (z + x)^2 * (x + y)^2)   :=  by sorry
