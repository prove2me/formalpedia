-- Prove2me | solution 1 for PositionalStratum.sum_positions
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:51:33.471817+00:00
-- url     : https://prove2.me/submissions/b56ea87a-c94f-415f-b1a1-251eb24841c3

-- Sol generated from Applications/PositionalStratumMeasure.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_mem_positions
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
theorem solution(M : ℕ) : ∑ i ∈ positions M, (i : ℝ) = (M : ℝ) * ((M : ℝ) + 1) / 2 := by
  induction M with
  | zero => simp [positions]
  | succ n ih =>
      have h : positions (n + 1) = insert (n + 1) (positions n) := by
        ext i
        simp only [mem_positions, Finset.mem_insert]
        omega
      rw [h, Finset.sum_insert (by simp [mem_positions]), ih]
      push_cast
      ring
