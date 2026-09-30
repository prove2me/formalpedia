-- Prove2me | solution 1 for lean_workbook_plus_15488
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:06:19.273885+00:00
-- url     : https://prove2.me/submissions/8bffc430-cb9c-4a79-881e-2c084f145594

import Mathlib.Analysis.Complex.Basic

theorem solution (p : ℕ) (hp : 3 < p) (hp1 : Nat.Prime p) : ∃ x y z : ℕ, x^2 + y^2 + z^2 = 4 * p^2 + 1 :=
  ⟨2 * p, 1, 0, by ring⟩
