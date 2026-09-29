-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_exists_not_routed
-- name    : Catalog.Probability.SeedRec.exists_not_routed
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:11:09.754885+00:00
-- url     : https://prove2.me/theorems/1c727c0e-fd02-42fb-ab30-21c93b9192fe
-- title:
--   No free lunch for the seed-compression router.
-- statement:
--   **No free lunch for the seed-compression router.** Once the file is a little
--   longer than the two model classes can describe, some file is rejected by *both*
--   detectors: seed compression cannot cover the file space.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.exists_not_routed(n : ℕ) (hK : 2 ≤ Fintype.card K)
--       (hL : 2 * L + 2 ≤ n) (hn : 5 ≤ n) :
--       ∃ x : Fin n → K, x ∉ lfsrWords K L n ∧ x ∉ lcgWords K n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGClassifier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGClassifier.lean#L110

-- Thm stub generated from Probability/PRNGClassifier.lean
import Mathlib
import Definitions.Def_Probability_PRNGClassifier
import Definitions.Def_Probability_PRNGLCGFingerprint
import Definitions.Def_Probability_PRNGLFSRDetection

/-!
# Finite-state periodicity and the limits of a seed-compression router

Two structural results about the classifier that routes a file to
*seed-compressible* or *model-compressible*.

**Positive side (why seed compression works at all).**  Any deterministic
generator with a finite state space is eventually periodic with preperiod plus
period at most `|S|`.  Hence its output stream — however long the file — is
completely determined by its first `|S|` symbols: `PRNG.stream_eq_early`.  This
is the structural reason a recovered seed reproduces the file exactly.

**Negative side (why the router cannot be a universal compressor).**  Combining
the counting bounds of the LFSR and LCG files: the union of the two families
covers at most `|K|^{2L} + |K|³` files of length `n`, so as soon as `n` exceeds
`2L` and `3` by a little, most files are rejected by *both* detectors:
`exists_not_routed`.  A seed-compression front end therefore never beats the
pigeonhole bound; it only reallocates code space.

Main contents.

* `PRNG.exists_iterate_collision` — pigeonhole on the state trajectory.
* `PRNG.exists_eventually_periodic` — preperiod `i` and period `p` with
  `i + p ≤ |S|`.
* `PRNG.stream_add_period_mul`, `PRNG.stream_eq_mod` — reduction of any time
  index into the fundamental window.
* `PRNG.stream_eq_early` — the whole stream is determined by its first `|S|`
  symbols.
* `routerWords`, `card_routerWords_le`, `exists_not_routed` — the two-family
  classifier still covers an exponentially small fraction of files.
-/

open Catalog.Probability.SeedRec

variable {S : Type*} {α : Type*} [Fintype S]



variable (g : PRNG S α) (s : S)





variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K] (L : ℕ)

theorem Catalog.Probability.SeedRec.exists_not_routed(n : ℕ) (hK : 2 ≤ Fintype.card K)
    (hL : 2 * L + 2 ≤ n) (hn : 5 ≤ n) :
    ∃ x : Fin n → K, x ∉ lfsrWords K L n ∧ x ∉ lcgWords K n := by sorry
