-- Prove2me | Theorems.Thm_generalized_fermat_equation
-- name    : generalized_fermat_equation
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:04:50.993736+00:00
-- url     : https://prove2.me/theorems/b1dfba0d-0a6a-4b79-b786-03f5cd55b16b
-- statement:
--   Generalized Fermat equation (Beal's conjecture): When 1/p + 1/q + 1/r < 1, a^p + b^q = c^r has only finitely many primitive solutions. Darmon–Granville proved finitely many for fixed p,q,r. Complete classification open.
-- source:
--   https://en.wikipedia.org/wiki/Beal%27s_conjecture

import Mathlib

import Mathlib

theorem generalized_fermat_equation (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hsum : (1 : ℚ)/p + 1/q + 1/r < 1) :
    {t : ℤ × ℤ × ℤ | t.1 ^ p + t.2.1 ^ q = t.2.2 ^ r ∧
      Nat.gcd t.1.natAbs (Nat.gcd t.2.1.natAbs t.2.2.natAbs) = 1}.Finite := by
  sorry
