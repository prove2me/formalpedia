-- Prove2me | Definitions.Def_Probability_PRNGNoiseTolerance
-- name    : Probability_PRNGNoiseTolerance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:17.002542+00:00
-- url     : https://prove2.me/theorems/2f7942f3-365f-478c-81f5-2c4ca24e8260
-- title:
--   Aether Catalog definitions — Probability_PRNGNoiseTolerance
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGNoiseTolerance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGNoiseTolerance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey

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

namespace Catalog.Probability.SeedRec

open Finset

variable {K : Type*} [CommRing K] {L n : ℕ}

section ErrorSet

variable [DecidableEq K]

/-- The set of positions at which the observed word `w` disagrees with the
candidate stream `y`: the corrupted symbols the detector must tolerate. -/
def errorSet (w : Fin n → K) (y : ℕ → K) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i ≠ y (i : ℕ)



end ErrorSet

/-! ## The refutation of C4 -/

section Counterexample




/-- The word used to refute C4: it takes the value `2` at index `1` and `1`
everywhere else. -/
def c4Word (e : ℕ) : Fin (2 * 1 + 2 * e + 1) → ZMod 3 := fun i => if (i : ℕ) = 1 then 2 else 1




/-! ### Sharpness of the corrected threshold at order one -/

/-- The word witnessing sharpness: `1` at even indices, `1` at the first `e` odd
indices and `2` at the last `e` odd indices — so it splits its disagreements
evenly between the constant stream and the alternating stream. -/
def sharpWord (e : ℕ) : Fin (4 * e + 1) → ZMod 3 :=
  fun i => if (i : ℕ) % 2 = 0 then 1 else if (i : ℕ) < 2 * e then 1 else 2





end Counterexample

/-! ## The corrected threshold -/

section Corrected


variable [Nontrivial K]



variable [DecidableEq K]


end Corrected

end Catalog.Probability.SeedRec


