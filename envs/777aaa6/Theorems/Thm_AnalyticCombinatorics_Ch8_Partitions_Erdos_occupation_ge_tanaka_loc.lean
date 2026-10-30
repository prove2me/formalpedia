-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_occupation_ge_tanaka_loc
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_tanaka_loc
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:27:23.883899+00:00
-- url     : https://prove2.me/theorems/88c292ac-4d6d-448d-9a13-83bd6ca71a17
-- title:
--   A finite-horizon off-window Tanaka occupation bound
-- statement:
--   Finite-horizon occupation upper comparison, off-window drift and bounded increments. No occupation divergence or positive global variance is assumed. P=K=identity on a singleton, D=0,b=eta=0 and point initial mass is a paper-level satisfying case.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem occupation_ge_tanaka_loc (K : α → α → ℝ) (D : α → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
--       (μ0 : α → ℝ) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
--       (hμ0sum : ∑ x, μ0 x = 1)
--       (hdrift_off : ∀ x, b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
--       (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (T : ℕ) :
--       (∑ x, distPow K μ0 T x * |D x|) - (∑ x, μ0 x * |D x|)
--         ≤ b * (∑ t ∈ Finset.range T,
--             ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η * T
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/LocalizedTanaka.lean#L62. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: localized (off-window) Tanaka occupation bound

The conditioned residual walk has a bounded REPELLING drift on the window, but is the product walk
(approximate martingale) OFF the window.  The Tanaka `|D|`-drift bound needs the drift `≤ η` only OFF the
window (`b < |D x|`); on-window the per-step `|D|`-drift is `≤ b` regardless of the drift (triangle
inequality).  So the occupation bound `E|D_T| − E|D_0| ≤ b·(window occupation) + η·T` holds with only the
off-window drift hypothesis.  Deterministic finite-sum.  Opus-authored.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)
include hPnn hPmass

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.occupation_ge_tanaka_loc (K : α → α → ℝ) (D : α → ℝ) (b η : ℝ) (hbnn : 0 ≤ b) (hηnn : 0 ≤ η)
    (μ0 : α → ℝ) (hμ0nn : ∀ x, 0 ≤ μ0 x) (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0sum : ∑ x, μ0 x = 1)
    (hdrift_off : ∀ x, b < |D x| → |(∑ z, K x z * D z) - D x| ≤ η)
    (hbinc : ∀ x z, K x z ≠ 0 → |D z - D x| ≤ b) (T : ℕ) :
    (∑ x, distPow K μ0 T x * |D x|) - (∑ x, μ0 x * |D x|)
      ≤ b * (∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ b then (1 : ℝ) else 0)) + η * T := by sorry
