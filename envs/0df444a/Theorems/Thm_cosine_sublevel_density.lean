-- Prove2me | Theorems.Thm_cosine_sublevel_density
-- name    : cosine_sublevel_density
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-26T11:29:15.361223+00:00
-- url     : https://prove2.me/theorems/903ced4b-0c66-5a50-ad2c-d383e01a806c
-- title:
--   Sublevel density of a single cosine vanishes as its mass grows
-- statement:
--   For every level $K$ and every tolerance $\rho > 0$ there is a mass threshold $M$ such that for every mass $m \ge M$ and every frequency $y > 0$, the Cesaro density over $[0,U]$ of the sublevel set $\{u : m(1-\cos(uy)) \le K\}$ is at most $\rho$ for all large $U$. The frequency is irrelevant by scaling; only the mass matters, since the sublevel set occupies a fraction about $\sqrt{K/m}$ of each period.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal

theorem cosine_sublevel_density :
  ∀ K : Real, ∀ ρ : ENNReal, 0 < ρ →
    ∃ M : Real, ∀ m y : Real, M ≤ m → 0 < y →
      ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
        (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (if m * (1 - Real.cos (u * y)) ≤ K then 1 else 0) ∂volume) * (ENNReal.ofReal U)⁻¹ ≤ ρ := by
  sorry
