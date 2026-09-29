-- Prove2me | solution 1 for SteinENT.bounded_rational_approximation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:26:45.717122+00:00
-- url     : https://prove2.me/submissions/acde31e3-8124-49f9-8399-3f4e0ce92316

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SteinENT

theorem _root_.solution (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ q : ℚ, 0 < q.den ∧ q.den ≤ n ∧
      |x - q| ≤ 1 / ((q.den : ℝ) * (n + 1)) := by
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hn
  exact ⟨q, q.pos, hden, by simpa [mul_comm] using hq⟩

end SteinENT
