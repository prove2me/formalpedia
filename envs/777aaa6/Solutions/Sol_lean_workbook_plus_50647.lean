-- Prove2me | solution 1 for lean_workbook_plus_50647
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:44:36.378138+00:00
-- url     : https://prove2.me/submissions/ab6aa86c-dc04-4c99-8852-0f62161d79e6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem rational_system_iff (p q r : ℚ) :
    (p = 7 / 10 + 3 / 10 * q ∧
      q = 7 / 10 * p + 3 / 10 * r ∧ r = 7 / 10 * q) ↔
    (p = 553 / 580 ∧ q = 49 / 58 ∧ r = 343 / 580) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem solution (p q r : ℚ)
    (h₀ : p = 7 / 10 + 3 / 10 * q)
    (h₁ : q = 7 / 10 * p + 3 / 10 * r)
    (h₂ : r = 7 / 10 * q) : q = 49 / 58 := by
  exact ((rational_system_iff p q r).mp ⟨h₀, h₁, h₂⟩).2.1

#print axioms solution
