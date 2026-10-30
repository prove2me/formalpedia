-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_fourth_moment_le_R4
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_R4
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:27:32.507656+00:00
-- url     : https://prove2.me/theorems/c83f868e-b872-4756-aea0-3cf6ec88cc84
-- title:
--   A finite-range fourth-moment bound
-- statement:
--   This separate public lemma bounds a finite probability fourth moment using only nonnegativity/stochasticity, initial mass1 and |D|<=R. It does not assume the impossible effective-variance premise of occupation_unbounded_eta. Singleton identity K, point initial mass,D=R=0 is a paper-level satisfying case.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma fourth_moment_le_R4 (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (R : ℝ)
--       (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hμ0nn : ∀ x, 0 ≤ μ0 x)
--       (hμ0sum : ∑ x, μ0 x = 1) (hR : ∀ x, |D x| ≤ R) (T : ℕ) :
--       (∑ x, distPow K μ0 T x * (D x) ^ 4) ≤ R ^ 4
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/OccupationEta.lean#L27. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TanakaTelescope
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: η-robust occupation capstone

For the η-approximate-martingale Erdős rank-difference walk, the window occupation is still unbounded.
The fourth moment is bounded *trivially* by `R⁴` (since `|D| ≤ R`), so Paley–Zygmund with the linear
lower QV `E[D_T²] ≥ (v₀−2Rη)·T` gives `(E|D_T|)² ≥ ((v₀−2Rη)T)³/R⁴ → ∞` (cubic) — no re-derived
fourth-moment bound needed.  Combined with the η-robust Tanaka bound `occ ≥ (E|D_T| − E|D_0| − ηT)/b`,
and since `E|D_T| ~ T^{3/2} ≫ ηT`, the occupation exceeds any target.  Deterministic finite-sum.
Opus-authored.
-/

set_option maxHeartbeats 1000000

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.fourth_moment_le_R4 (K : ι → ι → ℝ) (D : ι → ℝ) (μ0 : ι → ℝ) (R : ℝ)
    (hKnn : ∀ x z, 0 ≤ K x z) (hKsum : ∀ x, ∑ z, K x z = 1) (hμ0nn : ∀ x, 0 ≤ μ0 x)
    (hμ0sum : ∑ x, μ0 x = 1) (hR : ∀ x, |D x| ≤ R) (T : ℕ) :
    (∑ x, distPow K μ0 T x * (D x) ^ 4) ≤ R ^ 4 := by sorry
