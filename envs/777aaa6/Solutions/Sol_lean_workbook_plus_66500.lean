-- Prove2me | solution 1 for lean_workbook_plus_66500
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:28:38.56666+00:00
-- url     : https://prove2.me/submissions/edb1caaa-a8ff-42b9-b2a1-fdb4188096c7

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem square_difference_divisibility_bound (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hd : (a - b) ^ 2 ∣ a * b) : b < 3 * a := by
  have hs : (a - b) ^ 2 ≤ a * b := Int.le_of_dvd (mul_pos ha hb) hd
  by_contra h
  have hba : 3 * a ≤ b := by omega
  have hp : 0 ≤ b * (b - 3 * a) := mul_nonneg (le_of_lt hb) (by omega)
  nlinarith [sq_pos_of_pos ha]

theorem positive_square_difference_set_finite (M : Set ℕ)
    (hpos : ∀ a ∈ M, 0 < a)
    (hpair : M.Pairwise fun a b => ((a : ℤ) - (b : ℤ)) ^ 2 ∣ (a : ℤ) * (b : ℤ)) :
    M.Finite := by
  rcases M.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact Set.finite_empty
  refine (Set.finite_Iio (3 * a)).subset ?_
  intro b hb
  change b < 3 * a
  by_cases hba : b = a
  · subst b
    have hapos := hpos a ha
    omega
  have hbnd := square_difference_divisibility_bound (a : ℤ) (b : ℤ)
    (by exact_mod_cast hpos a ha) (by exact_mod_cast hpos b hb)
    (hpair ha hb (Ne.symm hba))
  exact_mod_cast hbnd

theorem solution (M : Set ℕ) (hM : M.Infinite)
    (hM' : M.PairwiseDisjoint fun (a : ℕ) (b : ℕ) => (a - b) ^ 2 ∣ a * b) : False := by
  have hsingle : M.Subsingleton := by
    intro a ha b hb
    by_contra hne
    have hdis := hM' ha hb hne
    have hzeroa : (a - 0) ^ 2 ∣ a * 0 := by simp
    have hzerob : (b - 0) ^ 2 ∣ b * 0 := by simp
    exact Set.disjoint_left.mp hdis hzeroa hzerob
  exact hM.not_finite hsingle.finite
