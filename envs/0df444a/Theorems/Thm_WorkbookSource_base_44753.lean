-- Prove2me | Theorems.Thm_WorkbookSource_base_44753
-- name    : WorkbookSource.base_44753
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:38.43296+00:00
-- url     : https://prove2.me/theorems/642e6704-b141-4e28-9a00-9c6a53d9a3cd
-- title:
--   A symmetric quartic inequality with a triple-product term
-- statement:
--   If $x,y,z$ are real numbers, then
--
--    $2(xy+yz+zx)(x^2+y^2+z^2)\le 3xyz(x+y+z)+4(x^4+y^4+z^4).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44753` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44753; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44753 (x y z : ℝ) : 2 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 3 * x * y * z * (x + y + z) + 4 * (x ^ 4 + y ^ 4 + z ^ 4)  :=  by sorry
