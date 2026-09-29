-- Prove2me | Theorems.Thm_mme_MM_induced_matching_quarter_root_absorption
-- name    : mme_MM_induced_matching_quarter_root_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:29:28.765307+00:00
-- url     : https://prove2.me/theorems/e9fc0648-03be-44fa-abc0-2d80d799035b
-- title:
--   Uniformly absorb the Behrend loss below H ≤ 4^N
-- statement:
--   For all sufficiently large \(N\), uniformly for every positive integer \(H\le4^N\),
--   \[
--   H^2\exp\!\left(-N(N+1)^{-1/4}\right)
--   \le
--   H^2\exp\!\left(-100\sqrt{\log(H+1)}\right).
--   \]
--
--   This comparison converts the explicit Behrend density loss into the fourth-root loss budget used by the coupled \(q=6\) certificate.  The uniformity follows from \(\log(H+1)=O(N)\), whereas \(N(N+1)^{-1/4}\) grows on the order of \(N^{3/4}\).
-- source:
--   Elementary asymptotic estimate used to absorb the explicit Behrend loss in the coupled Coppersmith--Winograd construction.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
open Filter Topology

theorem mme_MM_induced_matching_quarter_root_absorption :
    ∀ᶠ N : ℕ in atTop,
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      ∀ H : ℕ, 0 < H → H ≤ 4 ^ N →
        ((H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) ≤
          ((H : ℝ) ^ 2) *
            Real.exp (-100 *
              Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))) := by sorry
