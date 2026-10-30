-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject.sum_over_D_fibers
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:07:29.344668+00:00
-- url     : https://prove2.me/submissions/bc8cadc1-6659-463d-838d-e5c44aaf3d88

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

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject

variable {S : Type*}

end AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos AnalyticCombinatorics.Ch8.Partitions.Erdos.DProject
open Finset
variable {S : Type*}
theorem solution {Ω : Finset S} {π : S → ℝ} {D : S → ℤ} {I : Finset ℤ}
    (hΩD : ∀ s ∈ Ω, D s ∈ I) (φ : ℤ → ℝ) :
    (∑ d ∈ I, πD Ω π D d * φ d) = ∑ s ∈ Ω, π s * φ (D s) := by
  classical
  simp_rw [πD, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hpush : ∀ d, (if D s = d then π s else 0) * φ d = if D s = d then π s * φ d else 0 := by
    intro d; split <;> simp
  simp_rw [hpush]
  rw [Finset.sum_ite_eq I (D s) (fun d => π s * φ d), if_pos (hΩD s hs)]
