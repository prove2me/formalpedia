-- Prove2me | Definitions.Def_Probability_PRNGRecoveryAlgorithm
-- name    : Probability_PRNGRecoveryAlgorithm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:34.692772+00:00
-- url     : https://prove2.me/theorems/b653b773-70df-4955-a970-66b755ae94af
-- title:
--   Aether Catalog definitions — Probability_PRNGRecoveryAlgorithm
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGRecoveryAlgorithm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGRecoveryAlgorithm.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
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

namespace Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K] {L n : ℕ}

/-! ## The impulse word has maximal linear complexity -/

/-- The impulse word `0, 0, …, 0, 1` of length `n`. -/
def impulseWord (K : Type*) [CommRing K] (n : ℕ) : Fin n → K :=
  fun i => if (i : ℕ) + 1 = n then 1 else 0




section Counting

variable [Fintype K] [DecidableEq K]




end Counting

/-! ## The seed-recovery procedure -/

section Recovery

variable [Fintype K] [DecidableEq K]

/-- The seed a detector must try: by `lfsr_pref_eq_self` the first `L` symbols of
an LFSR output *are* its seed, so this is the only candidate. -/
def observedSeed (hL : L ≤ n) (x : Fin n → K) : Fin L → K :=
  fun i => x ⟨(i : ℕ), lt_of_lt_of_le i.isLt hL⟩


/-- The set of tap vectors accepted by the detector: those that regenerate the
whole observed word from the observed seed. -/
def candidateTaps (hL : L ≤ n) (x : Fin n → K) : Finset (Fin L → K) :=
  Finset.univ.filter fun c => (lfsrPRNG c).pref n (observedSeed hL x) = x


/-- The Boolean fingerprint test: does *some* order-`L` LFSR reproduce the file? -/
def lfsrDetect (hL : L ≤ n) (x : Fin n → K) : Bool :=
  decide (candidateTaps hL x).Nonempty





end Recovery

end Catalog.Probability.SeedRec


