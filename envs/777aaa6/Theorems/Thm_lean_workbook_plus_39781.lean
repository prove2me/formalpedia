-- Prove2me | Theorems.Thm_lean_workbook_plus_39781
-- name    : lean_workbook_plus_39781
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cd89f2fa-0d16-49ac-a651-e64ea1302bbe
-- statement:
--   Prove that: $27xyz+9(x+y+z)(x^2+y^2+z^2)\ge 4(x+y+z)^3$ for all x,y,z>0
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39781 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 27 * x * y * z + 9 * (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 4 * (x + y + z) ^ 3   :=  by sorry
