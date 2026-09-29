-- Prove2me | Theorems.Thm_AlmostLossless_failProb_le_of_correct_on
-- name    : AlmostLossless.failProb_le_of_correct_on
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:14:24.325987+00:00
-- url     : https://prove2.me/theorems/af2fa00b-91b9-4070-8a9b-796b61d9a7f9
-- title:
--   Generic achievability lemma.
-- statement:
--   **Generic achievability lemma.**  If a code decodes every word of a set `T`
--   of probability at least `1 - ε` correctly, it fails with probability at most
--   `ε`.  All achievability results below are instances of this.
--
--   ```lean
--   theorem AlmostLossless.failProb_le_of_correct_on[DecidableEq S] (μ : Source S) (K : Code S C)
--       (T : Finset S) (hcor : ∀ s ∈ T, Correct K s) (ε : ℚ) (hT : 1 - ε ≤ μ.prob T) :
--       failProb μ K ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Core.lean#L139

-- Thm stub generated from Logic/AlmostLossless/Core.lean
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

theorem AlmostLossless.failProb_le_of_correct_on[DecidableEq S] (μ : Source S) (K : Code S C)
    (T : Finset S) (hcor : ∀ s ∈ T, Correct K s) (ε : ℚ) (hT : 1 - ε ≤ μ.prob T) :
    failProb μ K ≤ ε := by sorry
