-- Prove2me | Theorems.Thm_lean_workbook_plus_66020
-- name    : lean_workbook_plus_66020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0b10c64f-5397-4d21-9464-88f1c596d1ea
-- statement:
--   Setting : $ {a + b = 1 + c + x ; c + b = 1 + a + y; c + a = 1 + b + z ; x,y,z \ge 0}$ The ineq equivalent to $ 18(xy + yz + zx) + 16xyz + 6(x^2 + y^2 + z^2) + 7[xy(x + y) + zy(z + y) + xz(x + z)] + 2(x^3 + y^3 + z^3) \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66020 {a b c x y z : ℝ} (ha : a + b = 1 + c + x) (hb : b + c = 1 + a + y) (hc : a + c = 1 + b + z) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : 18 * (x * y + y * z + z * x) + 16 * x * y * z + 6 * (x ^ 2 + y ^ 2 + z ^ 2) + 7 * (x * y * (x + y) + z * y * (z + y) + x * z * (x + z)) + 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ 0   :=  by sorry
