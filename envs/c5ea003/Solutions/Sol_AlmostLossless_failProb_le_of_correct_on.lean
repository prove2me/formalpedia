-- Prove2me | solution 1 for AlmostLossless.failProb_le_of_correct_on
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:10:31.464687+00:00
-- url     : https://prove2.me/submissions/1ecb8e8c-efab-4b99-b381-61525f9975e7

-- Sol generated from Logic/AlmostLossless/Core.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core

/-!
# Almost-lossless compression: the ε-relaxed counting bound

This file is the foundation of a small formal theory of *almost-lossless*
(one-shot, fixed-length) source compression.  The guiding question is the one
from the research thread *Compression Beyond the Pigeonhole Bound*:

> Pigeonhole governs exact decoding of **all** strings.  If we only ask that the
> decoder succeed with probability `≥ 1 - ε`, how far does the counting bound
> relax, and can a random number generator (shared randomness) help?

## Contents

* `AlmostLossless.Code` : an encoder/decoder pair `S → C → Option S`.
* `AlmostLossless.Honest` : *no silent corruption* — on every source word the
  decoder either returns the correct word or explicitly declares failure.
* `AlmostLossless.card_correct_le_card_code` : the pigeonhole core, the set of
  correctly decoded words injects into the code alphabet.
* `AlmostLossless.uniform_failProb_lower` : for a uniform source the failure
  probability is at least `1 - |C|/|S|`; equivalently
  `AlmostLossless.card_code_ge_of_failProb_le` : an `ε`-reliable code needs
  `|C| ≥ (1-ε)|S|`.  This is *exactly* how much the counting bound relaxes.
* `AlmostLossless.randomized_avg_failProb_lower` : the same bound holds for the
  average failure probability of an arbitrary **randomized** ensemble of codes,
  i.e. a random number generator buys nothing at all on a uniform source.
* `AlmostLossless.tableCode` and `AlmostLossless.failProb_tableCode_le` : the
  matching achievability statement.  Any *typical set* `T` of probability
  `≥ 1 - ε` yields an honest code with alphabet of size `|T| + 1` and failure
  probability `≤ ε`, with `O(1)` (single table lookup) decoding.

Everything is finite and rational-valued: probabilities are explicit finite
sums, so all statements are elementary and fully constructive in content.
-/

open AlmostLossless

open Finset


variable {S C : Type*}





/-! ## The pigeonhole core -/



/-! ## Sources and failure probability -/


variable [Fintype S]







/-! ## The ε-relaxed counting bound (converse) -/



/-! ## Randomness does not help on a uniform source -/




/-! ## Achievability: the typical-set table code -/






/-! ## The exact ε-relaxed pigeonhole principle -/






open AlmostLossless in
theorem solution[DecidableEq S] (μ : Source S) (K : Code S C)
    (T : Finset S) (hcor : ∀ s ∈ T, Correct K s) (ε : ℚ) (hT : 1 - ε ≤ μ.prob T) :
    failProb μ K ≤ ε := by
  classical
  have hsub : ({s | ¬ Correct K s} : Finset S) ⊆ Tᶜ := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Finset.mem_compl]
    intro hsT
    exact hs (hcor s hsT)
  have h1 : failProb μ K ≤ ∑ s ∈ Tᶜ, μ.w s :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => μ.nonneg s)
  have h2 : ∑ s ∈ Tᶜ, μ.w s = 1 - μ.prob T := by
    have := Finset.sum_add_sum_compl T μ.w
    rw [μ.total] at this
    simp only [Source.prob]
    linarith
  linarith
