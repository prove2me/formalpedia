-- Prove2me | solution 1 for lean_workbook_plus_61418
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:37:25.640836+00:00
-- url     : https://prove2.me/submissions/104d4b8d-c037-483e-8f02-81e0f67d9c7b

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace NaturalPowerLinearBound

theorem cubic_lower_bound (a : ℕ) (ha : 2 ≤ a) : 3 * (a + 1) ≤ a ^ 3 + 1 := by
  have hsq := Nat.mul_le_mul_right a ha
  have hcube := Nat.mul_le_mul_left (a ^ 2) ha
  nlinarith

theorem strict_step (a b : ℕ) (ha : 2 ≤ a) (hb : 3 ≤ b)
    (h : b * (a + 1) ≤ a ^ b + 1) : (b + 1) * (a + 1) < a ^ (b + 1) + 1 := by
  rw [pow_succ]
  have hp := Nat.mul_le_mul_left (a ^ b) ha
  have hbmul := Nat.mul_le_mul_right (a + 1) hb
  nlinarith

theorem lower_bound_offset (a k : ℕ) (ha : 2 ≤ a) :
    (k + 3) * (a + 1) ≤ a ^ (k + 3) + 1 := by
  induction k with
  | zero => simpa using cubic_lower_bound a ha
  | succ k ih =>
    change (k + 1 + 3) * (a + 1) ≤ a ^ (k + 1 + 3) + 1
    have hi : k + 1 + 3 = (k + 3) + 1 := by omega
    rw [hi]
    exact (strict_step a (k + 3) ha (by omega) ih).le

theorem lower_bound (a b : ℕ) (ha : 2 ≤ a) (hb : 3 ≤ b) :
    b * (a + 1) ≤ a ^ b + 1 := by
  simpa only [Nat.sub_add_cancel hb] using lower_bound_offset a (b - 3) ha

theorem equality_iff (a b : ℕ) (ha : 1 < a) (hb : 2 < b) :
    a ^ b + 1 = b * (a + 1) ↔ a = 2 ∧ b = 3 := by
  constructor
  · intro heq
    have hb3 : b = 3 := by
      by_contra hne
      have hprev : 3 ≤ b - 1 := by omega
      have hlow := lower_bound a (b - 1) (by omega) hprev
      have hstrict := strict_step a (b - 1) (by omega) hprev hlow
      have hi : b - 1 + 1 = b := by omega
      rw [hi] at hstrict
      omega
    subst b
    have hsq := Nat.mul_le_mul_right a (show 2 ≤ a by omega)
    have hcube := Nat.mul_le_mul_left (a ^ 2) (show 2 ≤ a by omega)
    have ha2 : a = 2 := by nlinarith
    exact ⟨ha2, rfl⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

end NaturalPowerLinearBound

theorem solution (a b : ℕ) (ha : a > 1) (hb : b > 2) :
    a ^ b + 1 ≥ b * (a + 1) := by
  exact NaturalPowerLinearBound.lower_bound a b (by omega) (by omega)

#print axioms NaturalPowerLinearBound.equality_iff
#print axioms solution
