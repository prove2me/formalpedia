-- Prove2me | Theorems.Thm_WorkbookSource_base_27236
-- name    : WorkbookSource.base_27236
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:35:32.363981+00:00
-- url     : https://prove2.me/theorems/93fa8027-2d7b-4497-a3a1-1eb037ccec66
-- title:
--   A cyclic fourth-degree inequality under linear substitutions
-- statement:
--   $x=2a-b,y=2b-c,z=2c-a$ then
--   $3(x^4+y^4+z^4-x^3y-y^3z-z^3x) \geq x^2(y-z)^2+y^2(z-x)^2+z^2(x-y)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27236` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27236; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27236 {x y z a b c : ℝ} (hx : x = 2 * a - b) (hy : y = 2 * b - c) (hz : z = 2 * c - a) : 3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ≥ x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 + z ^ 2 * (x - y) ^ 2  :=  by sorry
