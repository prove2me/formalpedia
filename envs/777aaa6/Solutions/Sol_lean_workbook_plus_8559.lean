-- Prove2me | solution 1 for lean_workbook_plus_8559
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:18.52447+00:00
-- url     : https://prove2.me/submissions/8106b9b3-4cc4-4aa3-8f8e-e968411f1f43

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ∀ n : ℕ, 3 ∣ 10^(n+1) + 10^n + 1 := by
  intro n
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
