-- Prove2me | Theorems.Thm_mme_behrend_log_loss_absorbed_sqrt
-- name    : mme_behrend_log_loss_absorbed_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:32:24.491304+00:00
-- url     : https://prove2.me/theorems/7818bcaa-a060-4f7e-a10d-eb3aec17d62d
-- title:
--   Absorption of Behrend logarithmic loss by a square-root source loss
-- statement:
--   If a finite fiber has size H≤4ᴺ, then its Behrend induced-matching loss exp(-100√log(H+1)) is at least exp(-200√(N+1)). Hence it can be absorbed into the square-root exponential error budget used in finite laser-method capacity estimates.
-- source:
--   Elementary analytic loss absorption used with Behrend induced matchings in the Coppersmith-Winograd laser method.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

theorem mme_behrend_log_loss_absorbed_sqrt
    (N H : ℕ) (hHbound : H ≤ 4 ^ N) :
    Real.exp (-200 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
      Real.exp (-100 *
        Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by
  sorry
