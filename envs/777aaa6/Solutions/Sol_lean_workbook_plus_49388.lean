-- Prove2me | solution 1 for lean_workbook_plus_49388
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:36.880506+00:00
-- url     : https://prove2.me/submissions/40afc20a-c640-4368-88d4-945dd05b0574

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (hxy : x + y + z = 20) (hxyz : x*y + y*z + z*x = 150) : False := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
