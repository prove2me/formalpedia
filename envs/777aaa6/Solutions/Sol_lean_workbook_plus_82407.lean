-- Prove2me | solution 1 for lean_workbook_plus_82407
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:44.372448+00:00
-- url     : https://prove2.me/submissions/518dba24-6283-4fc1-8c58-da02cdd71532

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y z : ℕ) (h₁ : x ≥ y) (h₂ : y ≥ z) :
    (Nat.floor (x * y / z) : ℕ) ≥ y * Nat.floor (x / z) := by
  simpa [Nat.mul_comm] using Nat.mul_div_le_mul_div_assoc y x z
