-- Prove2me | solution 1 for lean_workbook_plus_69642
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:18:40.194782+00:00
-- url     : https://prove2.me/submissions/4992a5ff-9a8f-4c28-be92-3cee245c23bd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
    (hz : 0 < z ∧ z < 1) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) :
    1 / 4 ≤ (1 - x) * y ∨ (1 - y) * z ≥ 1 / 4 ∨ (1 - z) * x ≥ 1 / 4 := by
  contrapose! h
  nlinarith
