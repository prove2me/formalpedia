-- Prove2me | Theorems.Thm_lean_workbook_plus_48018
-- name    : lean_workbook_plus_48018
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/52741fe8-7bb5-4132-b30b-4a31fe33f43e
-- statement:
--   Let $x,y,z> 0$ . Prove that: $2(x+y+z)^3+9xyz\geq 7(x+y+z)(xy+yz+zx)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48018 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 2 * (x + y + z) ^ 3 + 9 * x * y * z ≥ 7 * (x + y + z) * (x * y + y * z + z * x)   :=  by sorry
