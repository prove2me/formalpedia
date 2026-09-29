-- Prove2me | solution 1 for Catalog.Probability.SeedRec.card_lfsrWords_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:20:02.506169+00:00
-- url     : https://prove2.me/submissions/6c9da88e-dea3-4a55-81fe-393c035da8a3

-- Sol generated from Probability/PRNGLFSRDetection.lean
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












variable (K L)
variable [Fintype K] [DecidableEq K]








open Catalog.Probability.SeedRec in
omit [NeZero L] in
theorem solution(n : ℕ) :
    (lfsrWords K L n).card ≤ Fintype.card K ^ (2 * L) := by
  classical
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, two_mul, pow_add]
