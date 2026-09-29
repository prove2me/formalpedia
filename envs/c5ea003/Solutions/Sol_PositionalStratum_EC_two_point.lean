-- Prove2me | solution 1 for PositionalStratum.EC_two_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:51:33.044034+00:00
-- url     : https://prove2.me/submissions/71cd93bf-f877-4348-b0d5-bad2e8b7d6dc

-- Sol generated from Applications/PositionalStratumMeasure.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
/-
# Positional-stratum measure framework (GAP-L4)

A self-contained finite-measure framework for *positional strata* in one-shot
search / retrieval cost models.

The setting is elementary but the statements are the ones that carry the load:

* `positions M` — the ranked slots `1, …, M`;
* a *weight* `w : ℕ → ℝ`, the probability of the target sitting at a given slot;
* a *cost kernel* `c : ℕ → ℝ`, the number of probes charged when the target is resolved
  at that slot.  Two kernels matter: the **scan kernel** `c i = i` (sequential probing)
  and the **block-commitment kernel** (constant on each stratum), which is the one behind
  the certified law of `PositionalStratumCertifiedLaw`.

Main results.

* `rbar_identity` : the universal object,  `EC = P · r̄_R + (1 - P) · r̄_C`, an *exact*
  identity for every weight, every cost kernel and every stratum of nondegenerate mass.
* `theta_eq_one_of_uniform` / `uniform_of_forall_theta_eq_one` : the booking factor
  `Θ = r̄_R / (cell centre)` equals `1` on uniform cells, and if it equals `1` on
  *every* cell then the weight is uniform.  The single-cell converse is **false**:
  `theta_eq_one_not_uniform` is an explicit non-uniform witness with `Θ = 1`.
* `scan_cost_le_baseline` : the majorization / Chebyshev step — a descending (antitone)
  weight has expected scan cost at most the full-scan baseline `C₀ = (M+1)/2`.
* `exchange_inequality`, `sorted_le_of_antitone` : the rearrangement step.
* `exists_large_bucket`, `speedup_le_two_pow_kbits` : the `k_bits` (pigeonhole) branch.
* `master_inequality`, `master_inequality_of_filter` :
  `S ≤ min (1/(Λ·Θ·q̂)) (2^k/(Λ·Θ))`.
* `value_universality_fails` : the booked (uniform-cell) value law is **not** universal —
  off uniform cells the true speedup exceeds the booked one by an *unbounded* factor.
-/

open PositionalStratum

open Finset

noncomputable section

/-! ## The finite positional space -/












/-! ## The r̄-identity : the universal object -/



/-! ## The booking factor `Θ` : uniformity detection -/




/-! ## Majorization : the descending weight beats the baseline -/





/-! ## The `k_bits` branch : pigeonhole on the filter -/



/-! ## The master inequality -/



/-! ## Off uniform cells the *value* law is not universal -/















open PositionalStratum in
theorem solution{M a b : ℕ} {c : ℕ → ℝ} (hab : a ≠ b) (ha : a ∈ positions M)
    (hb : b ∈ positions M) (x y : ℝ) :
    EC M c (fun i => if i = a then x else if i = b then y else 0) = c a * x + c b * y := by
  classical
  rw [EC, Finset.sum_eq_add_of_mem a b ha hb hab ?_]
  · simp [hab.symm]
  · intro i _ hi
    simp [hi.1, hi.2]
