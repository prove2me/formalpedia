-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_DProjection
-- name    : AnalyticCombinatorics_Ch8_Partitions_DProjection
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:01:17.899991+00:00
-- url     : https://prove2.me/theorems/da137c64-c73b-46bf-8908-288daac53c08
-- title:
--   D Projection
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/DProjection.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject

variable {S : Type*}

/-- `D`-pushforward of the reference measure: total `π`-mass on the fiber `{D = d}`. -/
def πD (Ω : Finset S) (π : S → ℝ) (D : S → ℤ) (d : ℤ) : ℝ :=
  ∑ s ∈ Ω, if D s = d then π s else 0

end AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject


