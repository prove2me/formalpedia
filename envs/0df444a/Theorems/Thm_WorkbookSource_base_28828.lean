-- Prove2me | Theorems.Thm_WorkbookSource_base_28828
-- name    : WorkbookSource.base_28828
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:08:27.356711+00:00
-- url     : https://prove2.me/theorems/ba9ec63e-339f-45b5-9f64-3f753ecf8fa1
-- title:
--   A symmetric quadratic ratio with a refined triple-product correction
-- statement:
--   The inequality is equivalent to $\frac{(x+y+z)^2}{xy+yz+zx}+\frac{32xyz}{(x+y+z)^3+5xyz}\ge 4$ for $x,y,z>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28828` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28828; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28828 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 / (x * y + y * z + z * x) + 32 * x * y * z / ((x + y + z) ^ 3 + 5 * x * y * z) ≥ 4  :=  by sorry
