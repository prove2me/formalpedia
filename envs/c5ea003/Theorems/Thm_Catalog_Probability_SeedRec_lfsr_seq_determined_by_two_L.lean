-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_lfsr_seq_determined_by_two_L
-- name    : Catalog.Probability.SeedRec.lfsr_seq_determined_by_two_L
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:12:08.913606+00:00
-- url     : https://prove2.me/theorems/d545c3c9-7b6d-4862-94ee-ffc87e8d7d8d
-- title:
--   The `2L` theorem.
-- statement:
--   **The `2L` theorem.** Two sequences, each of linear complexity at most `L`
--   (possibly with *different* tap vectors), that agree on their first `2L` symbols
--   are equal at every index.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.lfsr_seq_determined_by_two_L[Nontrivial K] (c c' : Fin L → K) (y z : ℕ → K)
--       (hy : SatisfiesLFSR c y) (hz : SatisfiesLFSR c' z)
--       (hagree : ∀ t < 2 * L, y t = z t) : y = z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGBerlekampMassey.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGBerlekampMassey.lean#L145

-- Thm stub generated from Probability/PRNGBerlekampMassey.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLFSRDetection

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

theorem Catalog.Probability.SeedRec.lfsr_seq_determined_by_two_L[Nontrivial K] (c c' : Fin L → K) (y z : ℕ → K)
    (hy : SatisfiesLFSR c y) (hz : SatisfiesLFSR c' z)
    (hagree : ∀ t < 2 * L, y t = z t) : y = z := by sorry
