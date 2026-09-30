-- Prove2me | solution 1 for lean_workbook_plus_54051
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:39.710469+00:00
-- url     : https://prove2.me/submissions/988c842e-984c-450c-958a-fed9c615da4a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) : 133 ∣ 11^(n+2) + 12^(2*n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he : 11 ^ (n + 1 + 2) + 12 ^ (2 * (n + 1) + 1) =
        11 * (11 ^ (n + 2) + 12 ^ (2 * n + 1)) +
          133 * 12 ^ (2 * n + 1) := by
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
        pow_add (11 : ℕ) (n + 2) 1, pow_add (12 : ℕ) (2 * n + 1) 2]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right ih 11) (dvd_mul_right 133 _)

#print axioms solution
