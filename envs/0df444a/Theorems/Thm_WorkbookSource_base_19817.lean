-- Prove2me | Theorems.Thm_WorkbookSource_base_19817
-- name    : WorkbookSource.base_19817
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:42:17.85177+00:00
-- url     : https://prove2.me/theorems/d4cb423f-10f3-46fb-b34c-abef49abea96
-- title:
--   A squared pairwise ratio expression bounds a symmetric ratio
-- statement:
--   For $x,y, z$ positive real numbers:
--
--    $ \left[ 2 \left( \frac{x}{y+z}+\frac{y}{x+z}+\frac{z}{x+y} \right)-1 \right]^2 -1 \ge \frac{2(x+y+z)^2}{x^2+y^2+z^2+xy+yz+zx} \ \ ; $
--
--   Greetings!
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19817` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19817; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19817 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * (x / (y + z) + y / (x + z) + z / (x + y)) - 1)^2 - 1 ≥ 2 * (x + y + z)^2 / (x^2 + y^2 + z^2 + x * y + y * z + z * x)  :=  by sorry
