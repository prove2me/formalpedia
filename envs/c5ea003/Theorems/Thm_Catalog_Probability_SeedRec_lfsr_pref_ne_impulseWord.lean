-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_lfsr_pref_ne_impulseWord
-- name    : Catalog.Probability.SeedRec.lfsr_pref_ne_impulseWord
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:12:06.342028+00:00
-- url     : https://prove2.me/theorems/8b3d9efa-f09b-4d03-ac15-951641bda1e4
-- title:
--   No short LFSR produces the impulse word.
-- statement:
--   **No short LFSR produces the impulse word.**  Its first `L` symbols are all
--   zero, so the only candidate seed is the zero seed — which produces the all-zero
--   file, not the impulse.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.lfsr_pref_ne_impulseWord[Nontrivial K] (c σ : Fin L → K) (hL : L < n) :
--       (lfsrPRNG c).pref n σ ≠ impulseWord K n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGRecoveryAlgorithm.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGRecoveryAlgorithm.lean#L63

-- Thm stub generated from Probability/PRNGRecoveryAlgorithm.lean
import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGRecoveryAlgorithm
import Definitions.Def_Probability_PRNGRouterCapacity
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# A verified seed-recovery procedure, and the maximal-complexity obstruction

This file supplies the missing *algorithmic* half of the seed-compression
pipeline, together with a refutation of the length clause of conjecture **C2**
of `FUTURE_DIRECTIONS.md`.

## The impulse word

`impulseWord K n` is `0, 0, …, 0, 1`.  It is the extremal example for linear
complexity:

* `lfsr_pref_ne_impulseWord` / `impulseWord_not_mem_lfsrWords` — no LFSR of
  order `L < n` produces it, because the only seed compatible with its first
  `L` symbols is the zero seed, which produces the all-zero file
  (`lfsr_pref_zero`);
* `impulseWord_mem_lfsrWords_self` — order `n` does produce it, so its linear
  complexity is *exactly* `n`;
* `bm_half_length_bound_false` — hence the clause of C2 asking a
  Berlekamp–Massey routine to always return an order `L ≤ ⌈n/2⌉` *consistent
  with the observed window* is **false**: for `n ≥ 2` the impulse word is
  consistent with no such order.  The correct invariant is minimality of the
  returned order, not a bound of `⌈n/2⌉` (which holds only for windows that
  genuinely come from a short LFSR).

## The recovery procedure

* `observedSeed` — the candidate seed *is* the first `L` observed symbols
  (`lfsr_pref_eq_self`); nothing else has to be searched.
* `candidateTaps` — the finite set of tap vectors that reproduce the whole
  observed word from that seed; `lfsrDetect` is the corresponding Boolean test.
* `candidateTaps_sound` — **falsifiability gate**: an accepted tap vector
  reproduces the file symbol by symbol.
* `lfsrDetect_eq_true_iff` — **completeness**: the test accepts exactly the
  files of linear complexity `≤ L`, so the search over `|K|^L` tap vectors is
  exhaustive.
* `recovered_stream_unique` — **certified extrapolation**: once the window is at
  least `2L` long, *all* accepted candidates predict the same infinite stream,
  so the recovered generator is unambiguous beyond the observed data.
* `lfsrDetect_impulseWord` — the detector correctly rejects the maximal
  complexity word.
-/

open Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K] {L n : ℕ}

/-! ## The impulse word has maximal linear complexity -/

theorem Catalog.Probability.SeedRec.lfsr_pref_ne_impulseWord[Nontrivial K] (c σ : Fin L → K) (hL : L < n) :
    (lfsrPRNG c).pref n σ ≠ impulseWord K n := by sorry
