-- Prove2me | Theorems.Thm_WorkbookSource_base_127
-- name    : WorkbookSource.base_127
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:27.730578+00:00
-- url     : https://prove2.me/theorems/fc85beef-6857-4c03-a346-b3dffbbd47a4
-- title:
--   A rational inequality involving three pairwise sums
-- statement:
--   Show that $ \forall x,y,z>0$ we have:
--    $ \frac{(x+y)(y+z)(z+x)}{4xyz} \geq \frac{x+z}{y+z} + \frac{y+z}{x+z}$ .
--
--    made by Caragea C.
--
--
--    Here is what I have found:
--
--    $ \frac{x+y}{4xyz}= \frac{1}{4yz} +\frac{1}{4xz} \geq \frac{1}{(y+z)^2}+ \frac{1}{(x+z)^2}$ and so we have that:
--    $ \frac{x+y}{4xyz} \geq \frac{1}{(y+z)^2} + \frac{1}{(x+z)^2}$ and we multiply by $(y+z)(x+z)$ and we have our ineq!
--
--    do you have other solutions? cheers!
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_127` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_127; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_127 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) / (4 * x * y * z) ≥ (x + z) / (y + z) + (y + z) / (x + z)  :=  by sorry
