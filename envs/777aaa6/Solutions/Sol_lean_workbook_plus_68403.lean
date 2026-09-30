-- Prove2me | solution 1 for lean_workbook_plus_68403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:24.0835+00:00
-- url     : https://prove2.me/submissions/b7a2bc19-691e-4413-84f7-034f8f3fa097

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false

lemma eleven_power_linear_congruence (m : ℕ) :
    Nat.ModEq 100 (11 ^ m) (10 * m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hstep : Nat.ModEq 100 ((10 * m + 1) * 11) (10 * (m + 1) + 1) := by
      dsimp [Nat.ModEq]
      omega
    simpa only [pow_succ] using (ih.mul (Nat.ModEq.refl 11)).trans hstep

theorem solution (k : ℕ) (h₁ : k ≤ 9) (n : ℕ) :
    (11 ^ (10 * n + k)) % 100 = 10 * k + 1 := by
  have h := eleven_power_linear_congruence (10 * n + k)
  dsimp [Nat.ModEq] at h
  omega

#print axioms solution
