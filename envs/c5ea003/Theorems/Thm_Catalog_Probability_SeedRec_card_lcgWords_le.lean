-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_card_lcgWords_le
-- name    : Catalog.Probability.SeedRec.card_lcgWords_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:24.338538+00:00
-- url     : https://prove2.me/theorems/140f05d9-5ad8-488e-a6a0-ed1ae5746362
-- title:
--   The whole LCG family over `K` produces at most `|K|³` files of any given
-- statement:
--   The whole LCG family over `K` produces at most `|K|³` files of any given
--   length: multiplier, increment and seed are all it knows.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.card_lcgWords_le(n : ℕ) : (lcgWords K n).card ≤ Fintype.card K ^ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGLCGFingerprint.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGLCGFingerprint.lean#L88

-- Thm stub generated from Probability/PRNGLCGFingerprint.lean
import Mathlib
import Definitions.Def_Probability_PRNGLCGFingerprint
import Definitions.Def_Probability_PRNGLFSRDetection

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

theorem Catalog.Probability.SeedRec.card_lcgWords_le(n : ℕ) : (lcgWords K n).card ≤ Fintype.card K ^ 3 := by sorry
