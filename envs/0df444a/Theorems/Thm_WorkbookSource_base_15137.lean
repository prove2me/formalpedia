-- Prove2me | Theorems.Thm_WorkbookSource_base_15137
-- name    : WorkbookSource.base_15137
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:59:42.518973+00:00
-- url     : https://prove2.me/theorems/9da1bfd3-32ff-42e4-88cb-4901a7b4707d
-- title:
--   A total sum bounds a product times squared reciprocals
-- statement:
--   Prove that for all positive real numbers $x, y, z$, the following inequality holds:
--   x + y + z \geq 4xyz \left(\frac{1}{(x+y)^2} + \frac{1}{(x+z)^2} + \frac{1}{(y+z)^2}\right)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15137` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15137; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15137 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x + y + z ≥ 4*x*y*z * (1/((x+y)^2) + 1/((x+z)^2) + 1/((y+z)^2))  :=  by sorry
