-- Prove2me | Theorems.Thm_syracuseStep_le_of_certificate
-- name    : syracuseStep_le_of_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T21:47:38.975578+00:00
-- url     : https://prove2.me/theorems/966c8c88-051b-41c5-8c5a-9a5dbee9574d
-- title:
--   Upper bound for a Syracuse step from a power-of-two certificate
-- statement:
--   If $3x+1=2^a y$, then the accelerated Syracuse value of $x$ is at most $y$. The displayed power of two need not be maximal: removing the full two-adic factor can only produce a value no larger than the quotient certified here.
-- source:
--   Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, American Mathematical Monthly 92 (1985), 3–23, https://websites.umich.edu/~lagarias/3x%2B1.html; accelerated Syracuse map factorization certificate.

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem syracuseStep_le_of_certificate (a : ℕ) {x y : ℕ}
    (h : 3 * x + 1 = 2 ^ a * y) : syracuseStep x ≤ y := by sorry
