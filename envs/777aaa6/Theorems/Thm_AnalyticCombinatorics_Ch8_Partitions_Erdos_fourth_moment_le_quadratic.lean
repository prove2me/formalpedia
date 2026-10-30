-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_fourth_moment_le_quadratic
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_quadratic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:28:09.630145+00:00
-- url     : https://prove2.me/theorems/becbb1f1-91e4-4f76-bd62-ba8275ccce2f
-- title:
--   A finite martingale fourth-moment bound
-- statement:
--   Finite stochastic martingale with bounded increments and an initial probability mass; there is no strictly positive global variance premise. Identity kernel, singleton carrier, D=0 and b=0 provide a paper-level satisfying case.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem fourth_moment_le_quadratic (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b)
--       (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
--       (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
--       (T : ℕ) :
--       (∑ x, distPow K μ0 T x * (D x) ^ 4)
--         ≤ (∑ x, μ0 x * (D x) ^ 4) + 8 * b ^ 2 * (∑ x, μ0 x * (D x) ^ 2) * T
--           + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/OccupationAssembly.lean#L35. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: assembling the occupation lower bound

Closed-form fourth-moment bound `E[D_T⁴] ≤ E[D_0⁴] + 8b²E[D_0²]·T + 8b⁴·T² + 3b⁴·T` (substituting the
upper QV into the fourth-moment telescoping), plus the reusable local-variance bound `locVar ≤ b²`.
These feed the Paley–Zygmund anti-concentration to give `E|D_T| → ∞`, hence (via Tanaka) the window
occupation `→ ∞`.  Deterministic finite-sum.  Opus-authored.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_quadratic (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (b : ℝ) (hbnn : 0 ≤ b)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hmart : ∀ x, ∑ z, K x z * D z = D x)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4)
      ≤ (∑ x, μ0 x * (D x) ^ 4) + 8 * b ^ 2 * (∑ x, μ0 x * (D x) ^ 2) * T
        + 8 * b ^ 4 * (T : ℝ) ^ 2 + 3 * b ^ 4 * T := by sorry
