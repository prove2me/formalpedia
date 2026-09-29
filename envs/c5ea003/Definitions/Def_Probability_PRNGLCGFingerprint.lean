-- Prove2me | Definitions.Def_Probability_PRNGLCGFingerprint
-- name    : Probability_PRNGLCGFingerprint
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:26:37.138243+00:00
-- url     : https://prove2.me/theorems/2b03cdcc-74dd-4322-b800-c083d2d16fd2
-- title:
--   Aether Catalog definitions — Probability_PRNGLCGFingerprint
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGLCGFingerprint`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGLCGFingerprint.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# Linear congruential generators are order-two LFSRs

The second most common real-world PRNG family after the LFSR is the **linear
congruential generator** `x ↦ a*x + b` (`rand()`, `java.util.Random`, countless
game engines).  Superficially it is an affine map on a ring, not a shift
register over a field, so a fingerprinting pipeline would seem to need a
separate detector and a separate inversion routine.

The main theorem of this file says otherwise: *the full-output LCG stream
satisfies the order-two linear recurrence*
`x_{t+2} = (a+1) x_{t+1} - a x_t`,
so the **same** Berlekamp–Massey style detector that catches LFSRs catches
LCGs, and the seed `(x₀, a x₀ + b)` is recovered from two observed symbols.

Main contents.

* `lcgPRNG`, `lcg_stream_succ` — the LCG as a `PRNG` and its defining recursion.
* `lcg_satisfiesLFSR` — the fingerprint: the LCG stream obeys the order-`2`
  recurrence with taps `![-a, a+1]`.
* `lcg_seed_recovery` — the explicit order-`2` LFSR seed `![x₀, a x₀ + b]`
  reproduces the LCG stream **exactly** at every index.
* `lcg_detected` — an LCG stream always passes the order-`2` fingerprint test.
* `card_lcgWords_le`, `exists_not_lcgWord` — the LCG family covers at most
  `|K|³` files of each length, so almost no file is LCG-compressible.
-/

namespace Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K]

/-- The linear congruential generator `x ↦ a*x + b`, outputting its full state. -/
def lcgPRNG (a b : K) : PRNG K K := ⟨fun x => a * x + b, id⟩






section Counting

variable (K) [Fintype K] [DecidableEq K]

/-- The length-`n` files producible by *some* LCG over `K` from *some* seed. -/
def lcgWords (n : ℕ) : Finset (Fin n → K) :=
  Finset.univ.image fun p : K × K × K => (lcgPRNG p.1 p.2.1).pref n p.2.2




end Counting

end Catalog.Probability.SeedRec


