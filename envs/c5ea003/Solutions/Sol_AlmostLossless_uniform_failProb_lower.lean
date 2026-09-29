-- Prove2me | solution 1 for AlmostLossless.uniform_failProb_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:23:13.120692+00:00
-- url     : https://prove2.me/submissions/d0179d8f-ce97-4c5d-a153-47799ef4ad3c

-- Sol generated from Logic/AlmostLossless/Core.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Theorems.Thm_AlmostLossless_card_correct_le_card_code

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
theorem solution[DecidableEq S] [Nonempty S] [Fintype C] (K : Code S C) :
    1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ) ≤ failProb uniformSource K := by
  classical
  have hS : (0 : ℚ) < (Fintype.card S : ℚ) := by
    exact_mod_cast Fintype.card_pos (α := S)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset S)) (p := fun s => Correct K s)
  simp only [Finset.card_univ] at hsplit
  have hc := card_correct_le_card_code K
  have hcount : (Fintype.card S : ℚ) - (Fintype.card C : ℚ)
      ≤ (({s | ¬ Correct K s} : Finset S).card : ℚ) := by
    have e1 : ((({s | Correct K s} : Finset S).card : ℚ))
        + (({s | ¬ Correct K s} : Finset S).card : ℚ) = (Fintype.card S : ℚ) := by
      exact_mod_cast hsplit
    have e2 : ((({s | Correct K s} : Finset S).card : ℚ)) ≤ (Fintype.card C : ℚ) := by
      exact_mod_cast hc
    linarith
  have hfp : failProb uniformSource K
      = (({s | ¬ Correct K s} : Finset S).card : ℚ) / (Fintype.card S : ℚ) := by
    simp [failProb, uniformSource, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [hfp, le_div_iff₀ hS]
  have : (1 - (Fintype.card C : ℚ) / (Fintype.card S : ℚ)) * (Fintype.card S : ℚ)
      = (Fintype.card S : ℚ) - (Fintype.card C : ℚ) := by
    field_simp
  rw [this]
  exact hcount
