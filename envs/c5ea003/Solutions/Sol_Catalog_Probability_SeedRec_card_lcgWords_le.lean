-- Prove2me | solution 1 for Catalog.Probability.SeedRec.card_lcgWords_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:04:48.725335+00:00
-- url     : https://prove2.me/submissions/a4506846-7090-47ff-a305-28855a71d43e

-- Sol generated from Probability/PRNGLCGFingerprint.lean
import Mathlib
import Definitions.Def_Probability_PRNGLCGFingerprint
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

open Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K]








variable (K) [Fintype K] [DecidableEq K]







open Catalog.Probability.SeedRec in
theorem solution(n : ℕ) : (lcgWords K n).card ≤ Fintype.card K ^ 3 := by
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ, pow_succ, mul_comm]
