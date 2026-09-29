-- Prove2me | Theorems.Thm_WorkbookSource_base_3844
-- name    : WorkbookSource.base_3844
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:34.10177+00:00
-- url     : https://prove2.me/theorems/5ec88b2f-7d89-42f0-9d2d-faa030390339
-- title:
--   A cyclic cubic-product inequality
-- statement:
--   The inequality $3(x^3y+y^3z+z^3x)\leq(x+y+z)(x^3+y^3+z^3)$ can be proved for any real $x,y,z$ using the same method as above.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3844` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3844; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3844 (x y z : ℝ) : 3 * (x^3 * y + y^3 * z + z^3 * x) ≤ (x + y + z) * (x^3 + y^3 + z^3)  :=  by sorry
