-- Prove2me | solution 1 for AlmostLossless.epsilon_pigeonhole_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:19:29.305233+00:00
-- url     : https://prove2.me/submissions/1b35b1de-a976-430a-9a67-35bfebe2167c

-- Sol generated from Logic/AlmostLossless/Core.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Theorems.Thm_AlmostLossless_card_correct_le_card_code
import Theorems.Thm_AlmostLossless_failProb_le_of_correct_on

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

/-- The correct set carries probability `1 - failProb`. -/
theorem prob_correct_eq [DecidableEq S] (μ : Source S) (K : Code S C) :
    μ.prob ({s | Correct K s} : Finset S) = 1 - failProb μ K := by
  classical
  have h := Finset.sum_add_sum_compl ({s | Correct K s} : Finset S) μ.w
  rw [μ.total] at h
  have hc : (({s | Correct K s} : Finset S))ᶜ = ({s | ¬ Correct K s} : Finset S) := by
    ext s; simp
  rw [hc] at h
  simp only [Source.prob, failProb]
  linarith


omit [Fintype S] in
theorem correct_spreadCode [DecidableEq S] [DecidableEq C] {T : Finset S}
    (f : Fin T.card ↪ C) (c₀ : C) {s : S} (hs : s ∈ T) :
    Correct (spreadCode T f c₀) s := by
  have hex : ∃ i : Fin T.card, f i = f (T.equivFin ⟨s, hs⟩) := ⟨_, rfl⟩
  simp only [Correct, spreadCode, hs, dif_pos, hex]
  have : hex.choose = T.equivFin ⟨s, hs⟩ := f.injective hex.choose_spec
  rw [this]
  simp



open AlmostLossless in
theorem solution[DecidableEq S] [Fintype C] [DecidableEq C] [Nonempty C]
    (μ : Source S) (ε : ℚ) :
    (∃ K : Code S C, failProb μ K ≤ ε)
      ↔ ∃ T : Finset S, T.card ≤ Fintype.card C ∧ 1 - ε ≤ μ.prob T := by
  classical
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨({s | Correct K s} : Finset S), card_correct_le_card_code K, ?_⟩
    rw [prob_correct_eq]
    linarith
  · rintro ⟨T, hcard, hprob⟩
    have hemb : Nonempty (Fin T.card ↪ C) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    obtain ⟨f⟩ := hemb
    obtain ⟨c₀⟩ := ‹Nonempty C›
    exact ⟨spreadCode T f c₀,
      failProb_le_of_correct_on μ _ T (fun s hs => correct_spreadCode f c₀ hs) ε hprob⟩
