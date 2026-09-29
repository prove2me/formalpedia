-- Prove2me | Theorems.Thm_mme_finite_collision_budget_averaging_real
-- name    : mme_finite_collision_budget_averaging_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:16.611282+00:00
-- url     : https://prove2.me/theorems/984deaa8-d030-4d9c-9030-57037719102c
-- title:
--   A real aggregate collision budget yields one good finite state
-- statement:
--   Let $\Omega$ be a nonempty finite state space, let $G(\omega)$ and $B(\omega)$ be nonnegative integral good and bad counts, and let $L$ be a real residual target. If
--
--   $$
--   |\Omega|L+\sum_{\omega\in\Omega}B(\omega)\le\sum_{\omega\in\Omega}G(\omega),
--   $$
--
--   then some state satisfies
--
--   $$
--   B(\omega)+L\le G(\omega).
--   $$
--
--   The real-valued formulation allows an analytic loss such as $V\exp(-C\sqrt N)$ to pass directly through the finite averaging step without integer rounding.
-- source:
--   Elementary finite averaging principle; used in the affine-hash collision-deletion argument of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators

theorem mme_finite_collision_budget_averaging_real
    {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (good bad : Ω → ℕ) (L : ℝ)
    (hbudget :
      (Fintype.card Ω : ℝ) * L + ∑ ω, (bad ω : ℝ) ≤
        ∑ ω, (good ω : ℝ)) :
    ∃ ω, (bad ω : ℝ) + L ≤ (good ω : ℝ) := by
  sorry
