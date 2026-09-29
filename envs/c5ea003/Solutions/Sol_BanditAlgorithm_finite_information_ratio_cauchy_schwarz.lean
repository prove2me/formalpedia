-- Prove2me | solution 1 for BanditAlgorithm.finite_information_ratio_cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:35:58.841603+00:00
-- url     : https://prove2.me/submissions/d7a3bac5-c1b5-4430-baf9-5a598eef171c

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution {k : ℕ}
    (p gap info : Fin k → ℝ)
    (hpoint : ∀ a, 2 * gap a ^ 2 ≤ info a) :
    (∑ a, p a * gap a) ^ 2 ≤
      ((k : ℝ) / 2) * ∑ a, p a ^ 2 * info a := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun a : Fin k ↦ p a * gap a)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  calc
    (∑ a, p a * gap a) ^ 2 ≤
        (k : ℝ) * ∑ a, (p a * gap a) ^ 2 := by exact_mod_cast hcs
    _ ≤ (k : ℝ) * ∑ a, (p a ^ 2 * info a / 2) := by
      gcongr with a
      have ha := mul_le_mul_of_nonneg_left (hpoint a) (sq_nonneg (p a))
      nlinarith
    _ = ((k : ℝ) / 2) * ∑ a, p a ^ 2 * info a := by
      ring_nf
      rw [← Finset.sum_mul]
      ring

end BanditAlgorithm
