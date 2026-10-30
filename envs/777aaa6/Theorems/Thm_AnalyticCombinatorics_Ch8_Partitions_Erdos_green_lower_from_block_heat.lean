-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_green_lower_from_block_heat
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.green_lower_from_block_heat
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:19:48.052983+00:00
-- url     : https://prove2.me/theorems/09b88285-9187-48ca-98da-85b81b9c111e
-- title:
--   A conditional Green occupation lower bound from block heat
-- statement:
--   On a finite type with decidable equality, let $K$ be a nonnegative row-stochastic kernel and $\mu_0$ a nonnegative distribution of total mass one. Assume the stated second-moment bound up to $T/2$, the full block-heat lower estimate in the $\Lambda\sqrt{m+1}$ band, $\Lambda>0$, $2V\le\Lambda^2$, $c_0\ge0$, $T\ge16$ and $c\le c_0/8$. With every bound exactly as in the contract below, $$c\sqrt T\le\sum_{t<T}\sum_x(\mu_0K^t)(x)\,\mathbf1_{|D(x)|\le W}.$$ This implication does not supply the block-heat or second-moment estimates.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   theorem green_lower_from_block_heat
--       (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ)
--       (W Λ c0 V c : ℝ) (T : ℕ)
--       (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
--       (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
--       (hM2 : ∀ m, m ≤ T / 2 →
--         ∑ x, distPow K μ0 m x * (D x) ^ 2 ≤ V * ((m : ℝ) + 1))
--       (hΛpos : 0 < Λ) (hΛ : 2 * V ≤ Λ ^ 2)
--       (hc0 : 0 ≤ c0) (hT : 16 ≤ T) (hc : c ≤ c0 / 8)
--       (hblock : ∀ m, m ≤ T / 2 → 1 ≤ m → ∀ x,
--         |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) →
--           c0 / Real.sqrt ((m : ℝ) + 1)
--             ≤ ∑ y, distPow K (fun z => if z = x then 1 else 0) m y *
--                 (if |D y| ≤ W then (1 : ℝ) else 0)) :
--       c * Real.sqrt (T : ℝ)
--         ≤ ∑ t ∈ Finset.range T,
--             ∑ x, distPow K μ0 t x *
--               (if |D x| ≤ W then (1 : ℝ) else 0)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/GreenBridge.lean#L553. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Green lower bridge from block heat + second-moment tightness (renewal route B, Layer 1)

This is the *deterministic finite-sum* bridge of the two-layer split (ChatGPT R8):
given a per-block heat lower bound `hblock` (`c0/√(m+1) ≤` window mass from a tight start) and a
second-moment tightness bound `hM2` (`∑ distPow·D² ≤ V(m+1)`), the cumulative window occupation over
a horizon `T` is `≥ (c0/8)·√T`.  No probability/measure theory — pure `Finset` algebra:

* `good_mass_ge_half` — Chebyshev/Markov: ≥ ½ of the law sits in `{|D| ≤ Λ√(m+1)}`.
* `distPow_expect_comp` — Chapman–Kolmogorov in expectation form (induction on the recursive `distPow`).
* `even_time_windowMass_lower` — one even-time block: feed `hblock` from each good start.
* `sum_Icc_one_div_sqrt_succ_ge` + `sqrt_T_quarter_le_sqrt_half_minus_one` — the `∑ 1/√(m+1) ≥ √T/4`
  telescope (no integrals).
* `green_lower_from_block_heat` — the assembled bridge, constant `c ≤ c0/8`, needs `16 ≤ T`.

The remaining wall is the *Layer 2* input `hblock` itself (`erdos_rankdiff_block_heat_lower`); this file
discharges everything around it.  (Bridge authored via ChatGPT ac2 R8, verified against the repo
`distPow` API and rebuilt clean-3.)
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.green_lower_from_block_heat
    (K : α → α → ℝ) (D : α → ℝ) (μ0 : α → ℝ)
    (W Λ c0 V c : ℝ) (T : ℕ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1)
    (hμ0nn : ∀ x, 0 ≤ μ0 x) (hμ0sum : ∑ x, μ0 x = 1)
    (hM2 : ∀ m, m ≤ T / 2 →
      ∑ x, distPow K μ0 m x * (D x) ^ 2 ≤ V * ((m : ℝ) + 1))
    (hΛpos : 0 < Λ) (hΛ : 2 * V ≤ Λ ^ 2)
    (hc0 : 0 ≤ c0) (hT : 16 ≤ T) (hc : c ≤ c0 / 8)
    (hblock : ∀ m, m ≤ T / 2 → 1 ≤ m → ∀ x,
      |D x| ≤ Λ * Real.sqrt ((m : ℝ) + 1) →
        c0 / Real.sqrt ((m : ℝ) + 1)
          ≤ ∑ y, distPow K (fun z => if z = x then 1 else 0) m y *
              (if |D y| ≤ W then (1 : ℝ) else 0)) :
    c * Real.sqrt (T : ℝ)
      ≤ ∑ t ∈ Finset.range T,
          ∑ x, distPow K μ0 t x *
            (if |D x| ≤ W then (1 : ℝ) else 0) := by sorry
