-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_card_errorSet_sharpWord_const
-- name    : Catalog.Probability.SeedRec.card_errorSet_sharpWord_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:12.772175+00:00
-- url     : https://prove2.me/theorems/9eb9690e-e534-4df5-b2ce-bb8663f79e16
-- title:
--   Card errorSet sharpWord const
-- statement:
--   Formal statement of `Catalog.Probability.SeedRec.card_errorSet_sharpWord_const` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.card_errorSet_sharpWord_const(e : ℕ) :
--       (errorSet (sharpWord e) (fun _ => (1 : ZMod 3))).card ≤ e := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGNoiseTolerance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGNoiseTolerance.lean#L166

-- Thm stub generated from Probability/PRNGNoiseTolerance.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGNoiseTolerance

/-!
# Noise-tolerant fingerprinting: the `2L + 2e + 1` conjecture is false

Real files are only *nearly* PRNG output (headers, checksums, interleaved
metadata), so the seed-compression router needs a fingerprint test that
tolerates `e` corrupted symbols.  Conjecture **C4** of `FUTURE_DIRECTIONS.md`
proposed the Reed–Solomon-style bound: a window of length `n ≥ 2L + 2e + 1`
should determine the underlying order-`L` stream uniquely.

This file settles C4 **negatively** and repairs it.

* `errorSet` — the corrupted positions of an observed word relative to a
  candidate stream.
* `noise_tolerance_two_L_plus_two_e_false` — **C4 is false**, for every error
  budget `e ≥ 1`: over `ZMod 3` there are two *distinct* order-one streams and
  a word of length exactly `2·1 + 2e + 1` lying within Hamming distance `e` of
  both.  The counterexample is structural, not accidental: the two streams
  agree on every even index, so their disagreements are spread out and no
  window of length `2L` is error-free — precisely the failure mode flagged as
  the caveat when C4 was stated.
* `noise_tolerance_five_false` — the smallest instance (`e = 1`, `n = 5`).
* `lfsr_seq_determined_of_block` — the shifted `2L` theorem: agreement on *any*
  `2L` consecutive indices forces agreement from there on.
* `exists_error_free_block` — a pigeonhole: `2e` errors cannot meet all of the
  `2e + 1` disjoint blocks of length `2L`.
* `unique_decoding_of_long_window` — **corrected conjecture C4′**: window length
  `2L(2e + 1)` *does* suffice.  Two order-`L` streams within distance `e` of a
  common observed word agree from some index `j` with `j + 2L ≤ n` onwards.
* `unique_decoding_threshold_sharp_order_one` — the corrected threshold is
  **sharp** at `L = 1`: unique decoding still fails at length
  `4e + 1 = 2·1·(2e + 1) - 1`, one symbol short of it.

Together the results pin the truth at order one: the correct threshold for
noise-tolerant LFSR fingerprinting is *not* the linear `2L + 2e + 1` but exactly
the multiplicative `2L(2e + 1)`.
-/

open Catalog.Probability.SeedRec

open Finset

variable {K : Type*} [CommRing K] {L n : ℕ}


variable [DecidableEq K]





/-! ## The refutation of C4 -/









/-! ### Sharpness of the corrected threshold at order one -/

theorem Catalog.Probability.SeedRec.card_errorSet_sharpWord_const(e : ℕ) :
    (errorSet (sharpWord e) (fun _ => (1 : ZMod 3))).card ≤ e := by sorry
