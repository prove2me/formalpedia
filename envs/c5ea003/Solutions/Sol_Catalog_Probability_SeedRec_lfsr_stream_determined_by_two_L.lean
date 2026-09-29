-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_stream_determined_by_two_L
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:11.886233+00:00
-- url     : https://prove2.me/submissions/6690d244-c90b-4dee-9874-6c0f184f3cb5

-- Sol generated from Probability/PRNGBerlekampMassey.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Theorems.Thm_Catalog_Probability_SeedRec_lfsr_seq_determined_by_two_L
import Theorems.Thm_Catalog_Probability_SeedRec_satisfiesLFSR_stream

/-!
# How many symbols certify a recovered seed?  The `2L` theorem

Berlekamp–Massey recovers a length-`L` LFSR from an observed window.  The
practical question for a seed-compressor is: **after how many observed symbols
is the recovered generator guaranteed to reproduce the rest of the file?**  This
file answers it: `2L` symbols suffice, for the whole family at once.

The proof runs through the module structure of `ℕ → K` over the polynomial ring,
with `X` acting as the shift operator:

* `shiftEnd` — the shift as a `K`-linear endomorphism of `ℕ → K`;
* `aeval_shiftEnd_apply` — the action of a polynomial is the associated linear
  recurrence operator;
* `charPolyLFSR`, `satisfiesLFSR_iff_aeval` — a stream is an order-`L` LFSR
  stream (taps `c`) exactly when its characteristic polynomial annihilates it;
* `eq_zero_of_annihilated` — a sequence annihilated by a monic polynomial of
  degree `m` and vanishing on `[0, m)` vanishes identically (rigidity);
* `aeval_mul_sub_eq_zero` — the difference of two sequences with annihilators
  `f` and `g` is annihilated by `f * g` (this is where the two *different* tap
  vectors get merged);
* `lfsr_seq_determined_by_two_L` — **the `2L` theorem**: two sequences each of
  linear complexity `≤ L` that agree on the first `2L` symbols agree forever;
* `lfsr_stream_determined_by_two_L` — the same statement for the concrete
  generators: matching `2L` output symbols certifies the recovered seed *and*
  taps for the entire, arbitrarily long, file.

The computational counterpart is the saturation observed in
`ComputationalEvidence.md`: over `GF(2)` the number of length-`n` words of
linear complexity `≤ L` is strictly increasing in `n` until `n = 2L`, and
constant afterwards.
-/

open Catalog.Probability.SeedRec

open Polynomial

variable {K : Type*} [CommRing K]




variable {L : ℕ}











open Catalog.Probability.SeedRec in
theorem solution[Nontrivial K] [NeZero L]
    (c c' : Fin L → K) (σ σ' : Fin L → K)
    (hagree : ∀ t < 2 * L, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t) :
    ∀ t, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t := by
  have := lfsr_seq_determined_by_two_L c c' _ _ (satisfiesLFSR_stream c σ)
    (satisfiesLFSR_stream c' σ') hagree
  exact fun t => congrFun this t
