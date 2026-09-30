-- Prove2me | solution 1 for lean_workbook_plus_20857
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:58:15.794979+00:00
-- url     : https://prove2.me/submissions/1d637c82-ed60-4619-a63b-e8f4deeefaa8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace RationalRecurrenceClosedForm

theorem closed_form (p : ℕ → ℚ) (h0 : p 0 = 1)
    (hrec : ∀ n, p (n + 1) = 2 / 3 * p n + 1 / 3 * (1 - p n)) :
    ∀ n, p n = (1 + 3 ^ n) / (2 * 3 ^ n) := by
  intro n
  induction n with
  | zero => norm_num [h0]
  | succ n ih =>
      rw [hrec, ih, pow_succ]
      have hpow : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hpow] <;> ring

theorem recurrence_unique (p q : ℕ → ℚ) (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp : ∀ n, p (n + 1) = 2 / 3 * p n + 1 / 3 * (1 - p n))
    (hq : ∀ n, q (n + 1) = 2 / 3 * q n + 1 / 3 * (1 - q n)) : p = q := by
  funext n
  rw [closed_form p hp0 hp n, closed_form q hq0 hq n]

end RationalRecurrenceClosedForm

theorem solution (p : ℕ → ℚ) (h₀ : p 0 = 1)
    (h₁ : ∀ n, p (n + 1) = 2 / 3 * p n + 1 / 3 * (1 - p n)) :
    p 2010 = (1 + 3 ^ 2010) / (2 * 3 ^ 2010) := by
  exact RationalRecurrenceClosedForm.closed_form p h₀ h₁ 2010
