-- Prove2me | Theorems.Thm_mme_finite_collision_budget_averaging
-- name    : mme_finite_collision_budget_averaging
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:40:49.919203+00:00
-- url     : https://prove2.me/theorems/74fa1f7a-4799-4737-8246-7645ef94a5bc
-- title:
--   Aggregate collision budget yields one good finite state
-- statement:
--   Let $\Omega$ be a nonempty finite set of states, let $G(\omega)$ and $B(\omega)$ be nonnegative integral good and bad counts, and let $L$ be a target residual budget.  If
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
--   This is the deterministic averaging step used after summing target-survival and collision counts over all affine hash parameters.
-- source:
--   Elementary finite averaging principle; used in the affine-hash collision-deletion argument of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 260--261 and 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators

theorem mme_finite_collision_budget_averaging
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (good bad : Ω → ℕ) (L : ℕ)
    (hbudget : Fintype.card Ω * L + ∑ ω, bad ω ≤ ∑ ω, good ω) :
    ∃ ω, bad ω + L ≤ good ω := by
  sorry
