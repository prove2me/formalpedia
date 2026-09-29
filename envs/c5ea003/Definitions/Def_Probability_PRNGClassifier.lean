-- Prove2me | Definitions.Def_Probability_PRNGClassifier
-- name    : Probability_PRNGClassifier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:27:06.11899+00:00
-- url     : https://prove2.me/theorems/39838ae6-b01a-41e8-9553-3742d4d3d9cc
-- title:
--   Aether Catalog definitions — Probability_PRNGClassifier
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGClassifier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGClassifier.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.SeedRec

variable {S : Type*} {α : Type*} [Fintype S]



variable (g : PRNG S α) (s : S)




section Router

variable (K : Type*) [CommRing K] [Fintype K] [DecidableEq K] (L : ℕ)

/-- The files accepted by the two-family classifier: those explained by an
order-`L` LFSR or by a linear congruential generator. -/
def routerWords (n : ℕ) : Finset (Fin n → K) := lfsrWords K L n ∪ lcgWords K n



end Router

end Catalog.Probability.SeedRec


