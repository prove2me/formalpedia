-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_truncated_block_heat_transfer
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.truncated_block_heat_transfer
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:18:50.084746+00:00
-- url     : https://prove2.me/theorems/c324534d-fe39-42da-beb3-21ad196bd4a7
-- title:
--   A conditional truncated-kernel heat transfer bound
-- statement:
--   On a finite type with decidable equality, let $K,K_{\rm tr}$ be nonnegative row-stochastic kernels and $\mu_0$ a nonnegative unit-mass distribution. Assume the rowwise bound $\sum_z|K(x,z)-K_{\rm tr}(x,z)|\le\varepsilon$, the stated truncated heat lower bound $c_0/\sqrt{M+1}$, and $(\sum_{t<M}t)\varepsilon\le c_0/(2\sqrt{M+1})$. Then $$\frac{c_0}{2\sqrt{M+1}}\le\sum_{t<M}\sum_x(\mu_0K^t)(x)\mathbf1_{|D(x)|\le W}.$$ Every kernel, horizon and loss factor is retained; no producer for the truncated estimate is asserted.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   theorem truncated_block_heat_transfer
--       (K Ktr : α → α → ℝ) (μ0 : α → ℝ) (D : α → ℝ)
--       (W c0 ε : ℝ) (M : ℕ)
--       (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
--       (hKtrnn : ∀ x z, 0 ≤ Ktr x z) (hKtrsum : ∀ x, ∑ z, Ktr x z = 1)
--       (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
--       (hclose : ∀ x, (∑ z, |K x z - Ktr x z|) ≤ ε)
--       (htrunc :
--         c0 / Real.sqrt ((M : ℝ) + 1)
--           ≤ ∑ t ∈ Finset.range M,
--               ∑ x, distPow Ktr μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0))
--       (herr :
--         (∑ t ∈ Finset.range M, (t : ℝ)) * ε
--           ≤ c0 / (2 * Real.sqrt ((M : ℝ) + 1))) :
--       c0 / (2 * Real.sqrt ((M : ℝ) + 1))
--         ≤ ∑ t ∈ Finset.range M,
--             ∑ x, distPow K μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TruncationTransfer.lean#L75. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Truncation transfer (renewal route B, Layer-2 steps A & C)

The Erdős rank-difference kernel is soft/nonlocal, but its rank-drop tail is *exponential*
(`RankDropKer.Pker_rankDrop_tail_majorant`, `γ = C/60`).  The Layer-2 block-heat lower bound is
therefore proved for a *truncated* kernel (jumps capped at `L_m ≍ log m`, mass renormalized) and
transferred back to the real kernel via the banked `OccupationTransfer.occupation_transfer`
(`L¹`-distance `t·ε` over a horizon).  This file banks the two kernel-agnostic, finite-sum bridges:

* `normalize_truncate_L1_eq_two_tail` — the per-row `L¹` distance between a probability row and its
  normalized truncation `P' = P·1_Good/q` is exactly `2·τ`, where `τ` is the truncated tail mass.
* `truncated_block_heat_transfer` — a truncated block-heat lower bound `c0/√(M+1)` transfers to the
  real kernel as `c0/(2√(M+1))`, provided the cumulative `L¹` error `(∑_{t<M} t)·ε ≤ c0/(2√(M+1))`.

(Route + constants from ChatGPT ac2 R9, verified against the repo's `occupation_transfer` /
`Pker_rankDrop_tail_majorant`.)
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.truncated_block_heat_transfer
    (K Ktr : α → α → ℝ) (μ0 : α → ℝ) (D : α → ℝ)
    (W c0 ε : ℝ) (M : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hKtrnn : ∀ x z, 0 ≤ Ktr x z) (hKtrsum : ∀ x, ∑ z, Ktr x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hclose : ∀ x, (∑ z, |K x z - Ktr x z|) ≤ ε)
    (htrunc :
      c0 / Real.sqrt ((M : ℝ) + 1)
        ≤ ∑ t ∈ Finset.range M,
            ∑ x, distPow Ktr μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0))
    (herr :
      (∑ t ∈ Finset.range M, (t : ℝ)) * ε
        ≤ c0 / (2 * Real.sqrt ((M : ℝ) + 1))) :
    c0 / (2 * Real.sqrt ((M : ℝ) + 1))
      ≤ ∑ t ∈ Finset.range M,
          ∑ x, distPow K μ0 t x * (if |D x| ≤ W then (1 : ℝ) else 0) := by sorry
