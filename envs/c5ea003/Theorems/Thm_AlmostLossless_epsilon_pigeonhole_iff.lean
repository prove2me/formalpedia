-- Prove2me | Theorems.Thm_AlmostLossless_epsilon_pigeonhole_iff
-- name    : AlmostLossless.epsilon_pigeonhole_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:11.659757+00:00
-- url     : https://prove2.me/theorems/79026cb4-ed71-49d3-9393-03362bf88475
-- title:
--   The exact `ε`-relaxed pigeonhole principle.
-- statement:
--   **The exact `ε`-relaxed pigeonhole principle.**  A code alphabet `C` admits
--   an `ε`-reliable code for the source `μ` **iff** some set of at most `|C|` source
--   words carries probability at least `1 - ε`.  So the pigeonhole bound does not
--   simply relax by a factor: it relaxes to a statement about the *concentration*
--   of the source, and for a uniform source (where every set of size `|C|` has
--   probability `|C|/|S|`) this recovers `|C| ≥ (1-ε)|S|` exactly.
--
--   ```lean
--   theorem AlmostLossless.epsilon_pigeonhole_iff[DecidableEq S] [Fintype C] [DecidableEq C] [Nonempty C]
--       (μ : Source S) (ε : ℚ) :
--       (∃ K : Code S C, failProb μ K ≤ ε)
--         ↔ ∃ T : Finset S, T.card ≤ Fintype.card C ∧ 1 - ε ≤ μ.prob T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Core.lean#L326

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







/-! ## The ε-relaxed counting bound (converse) -/



/-! ## Randomness does not help on a uniform source -/




/-! ## Achievability: the typical-set table code -/






/-! ## The exact ε-relaxed pigeonhole principle -/

theorem AlmostLossless.epsilon_pigeonhole_iff[DecidableEq S] [Fintype C] [DecidableEq C] [Nonempty C]
    (μ : Source S) (ε : ℚ) :
    (∃ K : Code S C, failProb μ K ≤ ε)
      ↔ ∃ T : Finset S, T.card ≤ Fintype.card C ∧ 1 - ε ≤ μ.prob T := by sorry
