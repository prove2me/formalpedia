-- Prove2me | solution 1 for lean_workbook_plus_59049
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:04:18.078159+00:00
-- url     : https://prove2.me/submissions/18ac55da-30e1-4bb6-9abf-1e15355f48b6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MixedDegreeThreeSquares

theorem gap_identity (x y : ℝ) :
    2 * (x ^ 6 + y ^ 6 + x ^ 2 * y ^ 2 + x ^ 4 * y ^ 4 -
      (x ^ 4 * y + x ^ 2 * y ^ 5 + x ^ 5 * y ^ 2 + x * y ^ 4)) =
    (x ^ 3 - y ^ 3) ^ 2 + (x * y - x ^ 2 * y ^ 2) ^ 2 +
      (x ^ 3 + y ^ 3 - x * y - x ^ 2 * y ^ 2) ^ 2 := by ring

theorem inequality (x y : ℝ) :
    x ^ 4 * y + x ^ 2 * y ^ 5 + x ^ 5 * y ^ 2 + x * y ^ 4 ≤
      x ^ 6 + y ^ 6 + x ^ 2 * y ^ 2 + x ^ 4 * y ^ 4 := by
  nlinarith [gap_identity x y, sq_nonneg (x ^ 3 - y ^ 3),
    sq_nonneg (x * y - x ^ 2 * y ^ 2),
    sq_nonneg (x ^ 3 + y ^ 3 - x * y - x ^ 2 * y ^ 2)]

theorem equality_iff (x y : ℝ) :
    x ^ 6 + y ^ 6 + x ^ 2 * y ^ 2 + x ^ 4 * y ^ 4 =
      x ^ 4 * y + x ^ 2 * y ^ 5 + x ^ 5 * y ^ 2 + x * y ^ 4 ↔
        (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) := by
  constructor
  · intro h
    have hg := gap_identity x y
    have hs1 := sq_nonneg (x ^ 3 - y ^ 3)
    have hs2 := sq_nonneg (x * y - x ^ 2 * y ^ 2)
    have hs3 := sq_nonneg (x ^ 3 + y ^ 3 - x * y - x ^ 2 * y ^ 2)
    have hcubes : x ^ 3 = y ^ 3 := by nlinarith
    have hxy : x = y := (show Odd (3 : ℕ) by decide).pow_injective hcubes
    subst y
    have hcd : x ^ 2 = x ^ 4 := by nlinarith
    have hab : 2 * x ^ 3 = x ^ 2 + x ^ 4 := by nlinarith
    have hf : x ^ 2 * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hz | ho
    · have hx : x = 0 := eq_zero_of_pow_eq_zero hz
      exact Or.inl ⟨hx, hx⟩
    · have hx : x = 1 := by linarith
      exact Or.inr ⟨hx, hx⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

end MixedDegreeThreeSquares

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 6 + y ^ 6 + x ^ 2 * y ^ 2 + x ^ 4 * y ^ 4 ≥
      x ^ 4 * y + x ^ 2 * y ^ 5 + x ^ 5 * y ^ 2 + x * y ^ 4 :=
  MixedDegreeThreeSquares.inequality x y
