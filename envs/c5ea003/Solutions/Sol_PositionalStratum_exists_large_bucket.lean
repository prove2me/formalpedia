-- Prove2me | solution 1 for PositionalStratum.exists_large_bucket
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:59:25.272491+00:00
-- url     : https://prove2.me/submissions/9256ccab-054e-46da-a9b7-4b10bfb689fe

-- Sol generated from Applications/PositionalStratumMeasure.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_card_positions
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
theorem solution(M k : ℕ) (h : ℕ → ℕ)
    (hmaps : ∀ i ∈ positions M, h i ∈ Finset.range (2 ^ k)) :
    ∃ b ∈ Finset.range (2 ^ k),
      (M : ℝ) / (2 ^ k) ≤ (({i ∈ positions M | h i = b} : Finset ℕ).card : ℝ) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hmapsTo : ((positions M : Finset ℕ) : Set ℕ).MapsTo h (Finset.range (2 ^ k)) :=
    fun i hi => Finset.mem_coe.mpr (hmaps i (Finset.mem_coe.mp hi))
  have hcard : ∑ b ∈ Finset.range (2 ^ k), ({i ∈ positions M | h i = b} : Finset ℕ).card
      = (positions M).card := (Finset.card_eq_sum_card_fiberwise hmapsTo).symm
  have hsum : ((positions M).card : ℝ)
      = ∑ b ∈ Finset.range (2 ^ k), (({i ∈ positions M | h i = b} : Finset ℕ).card : ℝ) := by
    rw [← hcard]; push_cast; ring
  have hne : (Finset.range (2 ^ k)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (pow_pos (by norm_num) k)⟩
  have hlt : ∑ b ∈ Finset.range (2 ^ k), (({i ∈ positions M | h i = b} : Finset ℕ).card : ℝ)
      < ∑ _b ∈ Finset.range (2 ^ k), (M : ℝ) / (2 ^ k) :=
    Finset.sum_lt_sum_of_nonempty hne (fun b hb => hcon b hb)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  rw [card_positions] at hsum
  have hfin : (M : ℝ) < (M : ℝ) := by
    calc (M : ℝ)
        = ∑ b ∈ Finset.range (2 ^ k),
            (({i ∈ positions M | h i = b} : Finset ℕ).card : ℝ) := hsum
      _ < ((2 ^ k : ℕ) : ℝ) * ((M : ℝ) / 2 ^ k) := hlt
      _ = (M : ℝ) := by push_cast; field_simp
  exact lt_irrefl _ hfin
