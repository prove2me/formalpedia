-- Prove2me | solution 1 for BookSixth.borromean_fox_odd
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T23:51:09.222418+00:00
-- url     : https://prove2.me/submissions/b32aead9-4400-45bc-99d7-9a4f99d42f26

import Mathlib
import Definitions.Def_BookSixth

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open BookSixth

namespace BookFix

/-- For odd `n`, multiplication by `4` is invertible on `ZMod n`. -/
theorem isUnit_four {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) : IsUnit (4 : ZMod n) := by
  have hnz : NeZero n := ⟨by omega⟩
  have hcop : Nat.Coprime 4 n := by
    have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.2 hodd
    simpa using Nat.Coprime.pow_left 2 h2
  have := (ZMod.isUnit_iff_coprime 4 n).2 hcop
  simpa using this

theorem borromean_fox_odd (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (a b c : ZMod n) :
    BorromeanFox a b c ↔ a = b ∧ b = c := by
  have hu := isUnit_four hn hodd
  constructor
  · rintro ⟨e1, e2, e3⟩
    have k1 : (4 : ZMod n) * (b - a) = 0 := by linear_combination e1
    have k2 : (4 : ZMod n) * (c - b) = 0 := by linear_combination e2
    have hba : b - a = 0 := by
      rcases hu with ⟨u, hu'⟩
      have : (u : ZMod n) * (b - a) = 0 := by rw [hu']; exact k1
      simpa using (Units.mul_right_eq_zero u).1 this
    have hcb : c - b = 0 := by
      rcases hu with ⟨u, hu'⟩
      have : (u : ZMod n) * (c - b) = 0 := by rw [hu']; exact k2
      simpa using (Units.mul_right_eq_zero u).1 this
    exact ⟨(sub_eq_zero.1 hba).symm, (sub_eq_zero.1 hcb).symm⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> ring


end BookFix

open scoped BigOperators in
open BookSixth in
theorem solution (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) (a b c : ZMod n) :
    BorromeanFox a b c ↔ a = b ∧ b = c :=
  BookFix.borromean_fox_odd n hn hodd a b c
