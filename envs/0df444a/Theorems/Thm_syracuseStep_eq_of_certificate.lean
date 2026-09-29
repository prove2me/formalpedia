-- Prove2me | Theorems.Thm_syracuseStep_eq_of_certificate
-- name    : syracuseStep_eq_of_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T21:47:36.97031+00:00
-- url     : https://prove2.me/theorems/4f4dbf4e-8070-4b06-a3d3-e5f96abe348c
-- title:
--   Exact Syracuse step from a complete power-of-two certificate
-- statement:
--   Let $3x+1=2^a y$ with $y$ odd. Then the accelerated Syracuse map sends $x$ exactly to $y$. The oddness condition says that the displayed power $2^a$ is the complete power of two dividing $3x+1$, making this a reusable certificate for symbolic orbit calculations.
-- source:
--   Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, American Mathematical Monthly 92 (1985), 3–23, https://websites.umich.edu/~lagarias/3x%2B1.html; accelerated Syracuse map factorization certificate.

import Mathlib
import Definitions.Def_syracuseStep

open Nat

theorem syracuseStep_eq_of_certificate (a : ℕ) {x y : ℕ}
    (h : 3 * x + 1 = 2 ^ a * y) (hy : Odd y) : syracuseStep x = y := by sorry
