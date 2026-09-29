-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_lfsr_recurrence
-- name    : Catalog.Probability.SeedRec.lfsr_recurrence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:11:14.249784+00:00
-- url     : https://prove2.me/theorems/bd16fd80-a8f2-41a2-aaca-b3ddf139c4ff
-- title:
--   Fingerprint.
-- statement:
--   **Fingerprint.** Every LFSR stream satisfies its order-`L` linear recurrence.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.lfsr_recurrence(c : Fin L → K) (σ : Fin L → K) (t : ℕ) :
--       (lfsrPRNG c).stream σ (t + L)
--         = ∑ j : Fin L, c j * (lfsrPRNG c).stream σ (t + (j : ℕ)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGLFSRDetection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGLFSRDetection.lean#L78

-- Thm stub generated from Probability/PRNGLFSRDetection.lean
import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# LFSR fingerprinting, seed recovery, and the rarity of low linear complexity

This file instantiates the abstract seed-compressibility framework of
`Probability.PRNGSeedRecovery` at the most important PRNG family: the
**linear feedback shift register** of length `L` over a commutative ring `K`
(over `ZMod 2` this is the classical binary LFSR that Berlekamp–Massey attacks).

The state is a window `σ : Fin L → K`; the machine outputs `σ 0` and shifts,
refilling the last cell with the feedback `∑ j, c j * σ j`.

Main contents.

* `lfsrStep`, `lfsrPRNG` — the shift register as a `PRNG`.
* `lfsr_state_apply` — the **window lemma**: cell `i` of the state after `k`
  steps is the output at time `i + k`.  All later results rest on it.
* `lfsr_recurrence` — the generated stream satisfies the order-`L` linear
  recurrence: the *fingerprint* of the family.
* `lfsr_detect` — **detection is exact**: a stream is LFSR output for the tap
  vector `c` *iff* it satisfies the recurrence.  This is soundness *and*
  completeness of the fingerprint test.
* `lfsr_pref_eq_self`, `lfsr_pref_injective` — **seed recovery**: the first `L`
  output symbols literally *are* the seed, and the seed is unique.
* `lfsr_exact_reproduction` — the falsifiability gate: the recovered seed
  regenerates the whole stream, at every index, not just the observed window.
* `card_lfsrWords_le`, `exists_not_lfsrWord` — **rarity**: at most `|K|^(2L)` of
  the `|K|ⁿ` files have linear complexity `≤ L`, so for `n > 2L` most files are
  *not* seed-compressible by any LFSR of that order.
-/

open Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K] {L : ℕ}




variable [NeZero L]

theorem Catalog.Probability.SeedRec.lfsr_recurrence(c : Fin L → K) (σ : Fin L → K) (t : ℕ) :
    (lfsrPRNG c).stream σ (t + L)
      = ∑ j : Fin L, c j * (lfsrPRNG c).stream σ (t + (j : ℕ)) := by sorry
