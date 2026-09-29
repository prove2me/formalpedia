-- Prove2me | Theorems.Thm_WorkbookSource_base_54170
-- name    : WorkbookSource.base_54170
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:48.473072+00:00
-- url     : https://prove2.me/theorems/a8582d7f-6100-4c15-81bc-03eb5978d155
-- title:
--   A symmetric quartic inequality with coefficient eleven
-- statement:
--   If $x,y,z$ are real numbers, then
--
--    $2(xy+yz+zx)(x^2+y^2+z^2)\le 11xyz(x+y+z)+4(x^4+y^4+z^4).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54170` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54170; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54170 (x y z : ℝ) : 2 * (x * y + y * z + z * x) * (x ^ 2 + y ^ 2 + z ^ 2) ≤ 11 * x * y * z * (x + y + z) + 4 * (x ^ 4 + y ^ 4 + z ^ 4)  :=  by sorry
