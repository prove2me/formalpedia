-- Prove2me | solution 1 for lean_workbook_plus_53370
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:46.129482+00:00
-- url     : https://prove2.me/submissions/aa8fd994-1847-40c5-b202-133149e0ee95

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem cubic_mixed_difference (a b c d x : ℤ) :
    let p := fun t : ℤ => a * t ^ 3 + b * t ^ 2 + c * t + d
    p (x + 8) - p (x + 7) - p (x + 6) + p (x + 5) -
      p (x + 4) + p (x + 3) + p (x + 2) - p (x + 1) = 48 * a := by
  dsimp
  ring

theorem solution (f : ℤ → ℤ) (x : ℤ)
    (f_def : ∀ x, f x = 7 * x ^ 3 + 23 * x + 18) :
    f (x + 8) - f (x + 7) - f (x + 6) + f (x + 5) -
      f (x + 4) + f (x + 3) + f (x + 2) - f (x + 1) = 336 := by
  simp only [f_def]
  simpa using cubic_mixed_difference 7 0 23 18 x

#print axioms solution
