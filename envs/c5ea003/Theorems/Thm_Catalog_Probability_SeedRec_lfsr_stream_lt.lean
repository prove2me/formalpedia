-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_lfsr_stream_lt
-- name    : Catalog.Probability.SeedRec.lfsr_stream_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:36.459207+00:00
-- url     : https://prove2.me/theorems/1085d213-afa9-498e-9cd9-0a8848518c7a
-- title:
--   The seed is read off the first `L` outputs: output `k < L` is cell `k` of the seed.
-- statement:
--   The seed is read off the first `L` outputs: output `k < L` is cell `k` of the seed.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.lfsr_stream_lt(c : Fin L → K) (σ : Fin L → K) (k : ℕ) (h : k < L) :
--       (lfsrPRNG c).stream σ k = σ ⟨k, h⟩ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGLFSRDetection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGLFSRDetection.lean#L73

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


omit [NeZero L] in

theorem Catalog.Probability.SeedRec.lfsr_stream_lt(c : Fin L → K) (σ : Fin L → K) (k : ℕ) (h : k < L) :
    (lfsrPRNG c).stream σ k = σ ⟨k, h⟩ := by sorry
