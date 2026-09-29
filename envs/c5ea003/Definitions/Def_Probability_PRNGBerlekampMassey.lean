-- Prove2me | Definitions.Def_Probability_PRNGBerlekampMassey
-- name    : Probability_PRNGBerlekampMassey
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:26:39.423359+00:00
-- url     : https://prove2.me/theorems/e92754d9-ce61-4eca-994a-321ffbff8532
-- title:
--   Aether Catalog definitions — Probability_PRNGBerlekampMassey
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGBerlekampMassey`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGBerlekampMassey.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.SeedRec

open Polynomial

variable {K : Type*} [CommRing K]

/-- The shift operator on sequences, as a `K`-linear endomorphism. -/
def shiftEnd (K : Type*) [CommRing K] : Module.End K (ℕ → K) where
  toFun y := fun t => y (t + 1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl



variable {L : ℕ}

/-- The characteristic polynomial `X^L - ∑ c_j X^j` of the tap vector `c`. -/
noncomputable def charPolyLFSR (c : Fin L → K) : K[X] :=
  X ^ L - ∑ j : Fin L, C (c j) * X ^ (j : ℕ)









end Catalog.Probability.SeedRec


