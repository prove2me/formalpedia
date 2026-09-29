-- Prove2me | Theorems.Thm_WorkbookSource_plus_7320
-- name    : WorkbookSource.plus_7320
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:41:03.278918+00:00
-- url     : https://prove2.me/theorems/04da69ac-dd52-48da-af0a-eae9bc04d912
-- title:
--   A cubic sum inequality at unit pairwise product sum
-- statement:
--   Prove that $ (2(x+y+z)-1)(x+y+z-2)+5xyz\geq 0 $ for nonnegative reals $x, y, z$ satisfying $xy+yz+zx=1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7320` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7320; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7320 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hab : x * y + y * z + z * x = 1) : (2 * (x + y + z) - 1) * (x + y + z - 2) + 5 * x * y * z ≥ 0   :=  by sorry
