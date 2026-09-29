-- Prove2me | solution 1 for PositionalStratum.value_universality_fails
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:33.435885+00:00
-- url     : https://prove2.me/submissions/c3e1dbf1-d8d8-4510-b375-943d6f624159

-- Sol generated from Applications/PositionalStratumMeasure.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_headWitness_EC
import Theorems.Thm_PositionalStratum_mass_two_point_both
import Theorems.Thm_PositionalStratum_mass_two_point_left
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






lemma headWitness_eq (m : ℕ) :
    headWitness m
      = fun i => if i = 1 then 1 - 1 / (m : ℝ) else if i = m + 1 then 1 / (m : ℝ) else 0 := rfl

lemma headWitness_nonneg {m : ℕ} (hm : 1 ≤ m) (i : ℕ) : 0 ≤ headWitness m i := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [headWitness]
  split_ifs
  · rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  · positivity
  · exact le_rfl

/-- The witness realises the booked capture probability `P = 1 - 1/m` exactly. -/
lemma headWitness_mass_head {m : ℕ} (hm : 1 ≤ m) :
    mass (positions m) (headWitness m) = 1 - 1 / (m : ℝ) := by
  have hmem : (1 : ℕ) ∈ positions m := by rw [mem_positions]; omega
  have hnot : m + 1 ∉ positions m := by rw [mem_positions]; omega
  rw [headWitness_eq]
  exact mass_two_point_left hmem hnot _ _

lemma headWitness_mass_total {m : ℕ} (hm : 1 ≤ m) :
    mass (positions (2 * m)) (headWitness m) = 1 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : (1 : ℕ) ∈ positions (2 * m) := by rw [mem_positions]; omega
  have h2 : m + 1 ∈ positions (2 * m) := by rw [mem_positions]; omega
  have hne : (1 : ℕ) ≠ m + 1 := by omega
  rw [headWitness_eq, mass_two_point_both hne h1 h2]
  field_simp
  ring


lemma headWitness_booked {m : ℕ} (hm : 1 ≤ m) :
    bookedEC (2 * m) m (1 - 1 / (m : ℝ)) = ((m : ℝ) + 3) / 2 := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  rw [bookedEC]
  push_cast
  field_simp
  ring




open PositionalStratum in
theorem solution(B : ℝ) :
    ∃ (M m : ℕ) (P : ℝ) (w : ℕ → ℝ), 0 < m ∧ m < M ∧ 0 < P ∧ P < 1 ∧
      (∀ i, 0 ≤ w i) ∧
      mass (positions m) w = P ∧
      mass (positions M) w = 1 ∧
      0 < EC M scanCost w ∧
      B * EC M scanCost w < bookedEC M m P := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (max B 1)
  set m : ℕ := 8 * n + 8 with hmdef
  have hm : 1 ≤ m := by omega
  have hmR : (8 : ℝ) ≤ (m : ℝ) := by
    have : (8 : ℕ) ≤ m := by omega
    exact_mod_cast this
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hEC := headWitness_EC hm
  have hbk := headWitness_booked hm
  refine ⟨2 * m, m, 1 - 1 / (m : ℝ), headWitness m, by omega, by omega, ?_, ?_,
    headWitness_nonneg hm, headWitness_mass_head hm, headWitness_mass_total hm, ?_, ?_⟩
  · rw [sub_pos, div_lt_one hmpos]; linarith
  · have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
  · rw [hEC]; norm_num
  · rw [hEC, hbk]
    have hBn : B < (n : ℝ) := lt_of_le_of_lt (le_max_left B 1) hn
    have hnm : (m : ℝ) = 8 * (n : ℝ) + 8 := by rw [hmdef]; push_cast; ring
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hnm]
    linarith
