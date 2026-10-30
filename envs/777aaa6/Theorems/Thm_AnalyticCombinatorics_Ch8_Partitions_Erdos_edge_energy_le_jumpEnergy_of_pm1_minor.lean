-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_edge_energy_le_jumpEnergy_of_pm1_minor
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.edge_energy_le_jumpEnergy_of_pm1_minor
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:18:43.489752+00:00
-- url     : https://prove2.me/theorems/a3a51a9a-8d6b-46bb-8b39-fa98a4417d8b
-- title:
--   A nearest-neighbour energy comparison allowing zero minorization
-- statement:
--   Let $K_c:\mathbb Z^2\to\mathbb R$ be nonnegative, $f:\mathbb Z\to\mathbb R$, $L\in\mathbb N$, and $p\ge0$, including $p=0$. Assume both directed nearest-neighbour weights on every source interval edge are at least $p$. Then $$2p\,E_L(f)\le\sum_{d,e\in\{-L,\ldots,L\}}K_c(d,e)(f(e)-f(d))^2,$$ where $E_L$ is the source nearest-edge energy. This is a finite-window conditional comparison.
--
--   The local source models, scales or predicates are defined exactly by:
--
--   ```lean
--   def edgeEnergyInt (L : ℕ) (f : ℤ → ℝ) : ℝ := ∑ r ∈ intEdges L, edgeSq f r
--   ```
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   theorem edge_energy_le_jumpEnergy_of_pm1_minor
--       (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) (p : ℝ)
--       (hpnn : 0 ≤ p) (hKnn : ∀ d e, 0 ≤ Kc d e)
--       (hplus : ∀ r ∈ intEdges L, p ≤ Kc r (r + 1))
--       (hminus : ∀ r ∈ intEdges L, p ≤ Kc (r + 1) r) :
--       2 * p * edgeEnergyInt L f
--         ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/Ellipticity.lean#L186. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_DirichletForm
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_Ellipticity
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Nearest-neighbor ellipticity lower bound (renewal route B, Layer-2 Stage 3c lower)

The lower half of the Dirichlet-form sandwich (ChatGPT ac2 R12 + R13): a `±1` minorization
(`Kc r (r+1) ≥ p`, `Kc (r+1) r ≥ p`) forces the directed jump energy to dominate the nearest-neighbor
edge energy,

  `2p · ∑_r (f(r+1) − f r)² ≤ ∑_{d,e} Kc(d,e)·(f e − f d)²`.

Each undirected edge `(r,r+1)` collects `≥ 2p` from its two directed nearest-neighbor jumps; the two
NN masks are extracted from the full double sum via collapsing inner indicator sums (`sum_eq_single`)
and `sum_filter`.  Combined with `DirichletForm.bounded_jump_energy_le_edge_energy` this gives the full
form sandwich `2p·E_edge ≤ E_K ≤ 3B²·E_edge`.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.edge_energy_le_jumpEnergy_of_pm1_minor
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) (p : ℝ)
    (hpnn : 0 ≤ p) (hKnn : ∀ d e, 0 ≤ Kc d e)
    (hplus : ∀ r ∈ intEdges L, p ≤ Kc r (r + 1))
    (hminus : ∀ r ∈ intEdges L, p ≤ Kc (r + 1) r) :
    2 * p * edgeEnergyInt L f
      ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 := by sorry
