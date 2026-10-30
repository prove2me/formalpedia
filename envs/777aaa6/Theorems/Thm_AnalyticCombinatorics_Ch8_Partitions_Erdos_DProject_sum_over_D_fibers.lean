-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_DProject_sum_over_D_fibers
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject.sum_over_D_fibers
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:07:09.255377+00:00
-- url     : https://prove2.me/theorems/6681d7d9-2a91-438c-bb39-3eaf54a2ec9f
-- title:
--   A finite sum over rank-difference fibres
-- statement:
--   Only two conditional finite fibre-sum identities are declared; the prose mentions a full projected form equality as subsequent work. Do not promote these identities to a complete lumpability or sector reduction.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma sum_over_D_fibers {Ω : Finset S} {π : S → ℝ} {D : S → ℤ} {I : Finset ℤ}
--       (hΩD : ∀ s ∈ Ω, D s ∈ I) (φ : ℤ → ℝ) :
--       (∑ d ∈ I, πD Ω π D d * φ d) = ∑ s ∈ Ω, π s * φ (D s)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/DProjection.lean#L77. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_DProjection
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Weak `D`-projection of a pair walk onto an integer observable

The renewal sector route is a statement about the *pair* walk `KhatResPair` on states `α × α` with the
integer observable `D (x,y) = rnk x − rnk y`.  The pair walk is **not** lumpable w.r.t. `D` (it is not
a Markov function of `D`), so we cannot reduce it to a 1-D Markov chain.  But the *Dirichlet form*
pulls back: with the reference-weighted `D`-pushforward `πD` and the `D`-projected kernel `KD`, the
pair pullback form `pairAK` equals the 1-D form `aK πD KD`.  That lets the banked 1-D sector machinery
(`aK`, `aAnti`, `Jflow`, `divJ`, `Hcut`, `crossingTV`, `sector_bound_from_Hcut_on`,
`sector_bound_with_divergence_on`) apply verbatim, with no fragile pair-state Hardy reproof.

This file builds the projection **core** (generic over a state type `S` with observable `D : S → ℤ`):
the measures `πD`/`massD`/`KD`, the weighted identity `πD·KD = massD`, and the first fiber-regrouping
lemma `sum_over_D_fibers`.  (The full projection equality `pairAK = aK πD KD` builds on these.)

Reference: ChatGPT-Pro R18 chose this weak-projection route over a fresh pair-state reproof.
-/

open Finset

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject

variable {S : Type*}

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject.sum_over_D_fibers {Ω : Finset S} {π : S → ℝ} {D : S → ℤ} {I : Finset ℤ}
    (hΩD : ∀ s ∈ Ω, D s ∈ I) (φ : ℤ → ℝ) :
    (∑ d ∈ I, πD Ω π D d * φ d) = ∑ s ∈ Ω, π s * φ (D s) := by sorry
