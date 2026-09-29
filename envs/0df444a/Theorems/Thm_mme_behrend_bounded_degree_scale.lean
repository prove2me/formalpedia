-- Prove2me | Theorems.Thm_mme_behrend_bounded_degree_scale
-- name    : mme_behrend_bounded_degree_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:15:53.298706+00:00
-- url     : https://prove2.me/theorems/2313de31-fc22-4b25-bd77-b063972c9f0c
-- title:
--   An exponential-square-root scale makes Behrend density dominate degree $D$
-- statement:
--   Let $1\le D\le5^N$, set $r=\sqrt{N+1}$, and choose the integer interval length
--
--   $$
--   Q=\left\lceil D\exp(1000r)\right\rceil.
--   $$
--
--   Then $Q>0$ and
--
--   $$
--   6D\le Q\exp\bigl(-4\sqrt{\log Q}\bigr),\qquad 4Q\le D\exp(2000r).
--   $$
--
--   Thus the explicit Behrend lower bound at length $Q$ already exceeds six times any collision degree bounded by $5^N$, while a prime modulus obtained from Bertrand's postulate remains within an $\exp(2000\sqrt{N+1})$ loss. The constant $2000$ is intentionally conservative and is far below the $100000$ envelope used in the formal CW $2.376$ mission.
-- source:
--   Explicit rate arithmetic for Behrend's progression-free-set bound, used in the Salem--Spencer hashing step of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

theorem mme_behrend_bounded_degree_scale
    (N D : ℕ) (hD1 : 1 ≤ D) (hD5 : D ≤ 5 ^ N) :
    let r := Real.sqrt (((N + 1 : ℕ) : ℝ))
    let Q := Nat.ceil ((D : ℝ) * Real.exp (1000 * r))
    0 < Q ∧
      (6 * D : ℝ) ≤
        (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ∧
      (4 * Q : ℝ) ≤ (D : ℝ) * Real.exp (2000 * r) := by
  sorry
