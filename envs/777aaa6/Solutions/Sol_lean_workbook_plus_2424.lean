-- Prove2me | solution 1 for lean_workbook_plus_2424
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:23:10.905766+00:00
-- url     : https://prove2.me/submissions/38bb7bf0-2946-4b5d-b9af-808b13295057

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MinusSevenPowerTwoSquare

theorem lift (r : ℕ) : ∃ x q : ℕ, Odd x ∧ x ^ 2 + 7 = 2 ^ (r + 3) * q := by
  induction r with
  | zero => exact ⟨1, 1, by norm_num, by norm_num⟩
  | succ r ih =>
      obtain ⟨x, q, hx, heq⟩ := ih
      obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' q
      · subst q
        refine ⟨x, t, hx, ?_⟩
        norm_num [pow_add] at heq ⊢
        nlinarith [heq]
      · subst q
        obtain ⟨u, rfl⟩ := hx
        refine ⟨2 * u + 1 + 2 ^ (r + 2), t + u + 1 + 2 ^ r, ?_, ?_⟩
        · refine ⟨u + 2 ^ (r + 1), ?_⟩
          norm_num [pow_add] <;> omega
        · norm_num [pow_add] at heq ⊢
          nlinarith [heq]

theorem positive_solution (k : ℕ) :
    ∃ n x : ℕ, 0 < n ∧ 0 < x ∧ Odd x ∧ n * 2 ^ k = x ^ 2 + 7 := by
  obtain ⟨x, q, hx, heq⟩ := lift k
  have hxpos : 0 < x := by
    obtain ⟨u, hu⟩ := hx
    omega
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, mul_zero] at heq
    omega
  refine ⟨8 * q, x, by omega, hxpos, hx, ?_⟩
  norm_num [pow_add] at heq
  nlinarith [heq]

end MinusSevenPowerTwoSquare

theorem solution (k : ℕ) : ∃ n : ℕ, ∃ x : ℕ, n * 2 ^ k - 7 = x ^ 2 := by
  obtain ⟨n, x, _, _, _, heq⟩ := MinusSevenPowerTwoSquare.positive_solution k
  exact ⟨n, x, by omega⟩
