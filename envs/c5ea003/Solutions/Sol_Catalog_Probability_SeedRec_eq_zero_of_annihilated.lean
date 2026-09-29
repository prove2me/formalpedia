-- Prove2me | solution 1 for Catalog.Probability.SeedRec.eq_zero_of_annihilated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:15:38.437556+00:00
-- url     : https://prove2.me/submissions/91af163c-8f74-4820-9a1b-f700d9653ec1

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

/-- Acting by a polynomial is applying the corresponding linear recurrence
operator to the sequence. -/
theorem aeval_shiftEnd_apply (p : K[X]) (y : ℕ → K) (t : ℕ) :
    (aeval (shiftEnd K) p) y t = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * y (t + i) := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  simp [shiftEnd_pow_apply]

variable {L : ℕ}











open Catalog.Probability.SeedRec in
theorem solution(p : K[X]) (hm : p.Monic) (w : ℕ → K)
    (hw : aeval (shiftEnd K) p w = 0) (hvan : ∀ t < p.natDegree, w t = 0) : w = 0 := by
  funext t
  show w t = 0
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      by_cases ht : t < p.natDegree
      · exact hvan t ht
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + p.natDegree := ⟨t - p.natDegree, by omega⟩
        have h0 : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * w (t' + i) = 0 := by
          have := congrFun hw t'
          rwa [aeval_shiftEnd_apply] at this
        rw [Finset.sum_range_succ, hm.coeff_natDegree, one_mul] at h0
        have hz : ∑ i ∈ Finset.range p.natDegree, p.coeff i * w (t' + i) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          rw [Finset.mem_range] at hi
          rw [ih (t' + i) (by omega), mul_zero]
        rw [hz, zero_add] at h0
        exact h0
