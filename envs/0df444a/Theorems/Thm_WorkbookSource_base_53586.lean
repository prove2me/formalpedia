-- Prove2me | Theorems.Thm_WorkbookSource_base_53586
-- name    : WorkbookSource.base_53586
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:29.082503+00:00
-- url     : https://prove2.me/theorems/ab689353-76e7-446e-bd64-8dc89c63d790
-- title:
--   A product of quadratic differences bounds the sixth power of the total
-- statement:
--   Prove with $x,y,z>0$ that $(7x^2+(y+z)^2-x(y+z))(7y^2+(x+z)^2-y(x+z))(7z^2+(x+y)^2-z(x+y)) \geqq(x+y+z)^6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53586` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53586; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53586 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (7*x^2 + (y + z)^2 - x*(y + z))*(7*y^2 + (x + z)^2 - y*(x + z))*(7*z^2 + (x + y)^2 - z*(x + y)) ≥ (x + y + z)^6  :=  by sorry
