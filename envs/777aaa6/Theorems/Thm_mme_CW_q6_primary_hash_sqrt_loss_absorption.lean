-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_sqrt_loss_absorption
-- name    : mme_CW_q6_primary_hash_sqrt_loss_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:06:31.227901+00:00
-- url     : https://prove2.me/theorems/600ec6d2-3caa-4694-b73e-1bdb175f128e
-- title:
--   Fourth-root slack absorbs every fixed square-root hashing loss
-- statement:
--   For every fixed constant $C≥0$, both fourth-root loss envelopes used by the q=6 counting theorem eventually dominate the square-root exponential loss:
--
--   $$e^{-N/(12 sqrt(sqrt(N+1)))} ≤ e^{-C sqrt(N+1)},$$
--
--   $$e^{-N/(8 sqrt(sqrt(N+1)))} ≤ e^{-C sqrt(N+1)}.$$
--
--   Thus any finite Salem-Spencer hashing and uniformization argument with loss $e^{-O(sqrt N)}$ fits simultaneously inside the mission's separately allocated outer and middle fourth-root budgets.
-- source:
--   Elementary asymptotic comparison: N^(3/4) dominates C*N^(1/2) for every fixed C. This is the analytic loss-allocation step accompanying the finite q=6 hashing construction of Coppersmith-Winograd 1990, journal p. 271, https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Topology

theorem mme_CW_q6_primary_hash_sqrt_loss_absorption
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      Real.exp (-((N : ℝ) * loss / 12)) ≤
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ∧
      Real.exp (-((N : ℝ) * loss / 8)) ≤
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by sorry
