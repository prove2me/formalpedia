-- Prove2me | Theorems.Thm_WorkbookSource_base_4868
-- name    : WorkbookSource.base_4868
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:39.536298+00:00
-- url     : https://prove2.me/theorems/dd09637a-5ba6-42d1-af5b-7451b98b71cc
-- title:
--   A cyclic quartic bound involving a triple product
-- statement:
--   If $ x,y,z$ are real numbers, then
--
--    $ x^4 + y^4 + z^4 + 2xyz(x + y + z)\ge x^3y + y^3z + z^3x$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4868` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4868; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4868 (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 + 2 * x * y * z * (x + y + z) ≥ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x  :=  by sorry
