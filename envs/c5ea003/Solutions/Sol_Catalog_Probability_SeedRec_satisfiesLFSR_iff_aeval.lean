-- Prove2me | solution 1 for Catalog.Probability.SeedRec.satisfiesLFSR_iff_aeval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:20:46.399153+00:00
-- url     : https://prove2.me/submissions/3632c331-e583-431b-bd48-a39826b5da03

-- Sol generated from Probability/PRNGBerlekampMassey.lean
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


theorem shiftEnd_pow_apply (y : ℕ → K) (i t : ℕ) : ((shiftEnd K) ^ i) y t = y (t + i) := by
  induction i generalizing y t with
  | zero => simp
  | succ i ih =>
      rw [pow_succ]
      show ((shiftEnd K) ^ i) ((shiftEnd K) y) t = _
      rw [ih]
      show y (t + i + 1) = y (t + (i + 1))
      ring_nf


variable {L : ℕ}











open Catalog.Probability.SeedRec in
theorem solution(c : Fin L → K) (y : ℕ → K) :
    SatisfiesLFSR c y ↔ aeval (shiftEnd K) (charPolyLFSR c) y = 0 := by
  have hval : ∀ t : ℕ, (aeval (shiftEnd K) (charPolyLFSR c)) y t
      = y (t + L) - ∑ j : Fin L, c j * y (t + (j : ℕ)) := by
    intro t
    simp [charPolyLFSR, map_sub, map_sum, shiftEnd_pow_apply]
  constructor
  · intro h
    funext t
    rw [hval t, h t, sub_self]
    rfl
  · intro h t
    have := congrFun h t
    rw [hval t] at this
    have h0 : (0 : ℕ → K) t = 0 := rfl
    rw [h0] at this
    exact sub_eq_zero.mp this
