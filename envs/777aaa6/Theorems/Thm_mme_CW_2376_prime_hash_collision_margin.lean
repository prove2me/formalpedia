-- Prove2me | Theorems.Thm_mme_CW_2376_prime_hash_collision_margin
-- name    : mme_CW_2376_prime_hash_collision_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:31:35.258617+00:00
-- url     : https://prove2.me/theorems/4bb81cd6-53f2-4ab7-8f64-971c3ea2cd43
-- title:
--   The prime Behrend set pays the full CW profile collision margin
-- statement:
--   Let $D_*$ be the target-profile completion degree and let $D$ be the full compatible completion degree at word length $N$. Suppose
--
--   $$
--   1\le D\le(N+1)^{15}D_*.
--   $$
--
--   If an affine-hash modulus $p$ and a progression-free label set $S$ satisfy
--
--   $$
--   |S|\ge6D,\qquad p\le D\exp\bigl(2000\sqrt{N+1}\bigr),
--   $$
--
--   then
--
--   $$
--   p^2\exp\bigl(-100000\sqrt{N+1}\bigr)+3D_*D\le D_*|S|.
--   $$
--
--   Thus the label density pays all three directed target-to-ambient collision budgets and still leaves the square-root exponential reserve required by the outer Coppersmith--Winograd $2.376$ profile.
-- source:
--   Finite normalization of the affine-hash collision estimate in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Exp

theorem mme_CW_2376_prime_hash_collision_margin
    (N D Dstar p S : ℕ)
    (hD1 : 1 ≤ D)
    (hDdom : D ≤ (N + 1) ^ 15 * Dstar)
    (hS : (6 * D : ℝ) ≤ (S : ℝ))
    (hp : (p : ℝ) ≤ (D : ℝ) *
      Real.exp (2000 * Real.sqrt (((N + 1 : ℕ) : ℝ)))) :
    (p : ℝ) ^ 2 *
          Real.exp (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) +
        3 * (Dstar : ℝ) * (D : ℝ) ≤
      (Dstar : ℝ) * (S : ℝ) := by
  sorry
