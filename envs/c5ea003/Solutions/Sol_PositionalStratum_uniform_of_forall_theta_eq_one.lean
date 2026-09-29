-- Prove2me | solution 1 for PositionalStratum.uniform_of_forall_theta_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:32.975917+00:00
-- url     : https://prove2.me/submissions/6532d4de-a63a-4096-9e42-6a211bef1da2

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
theorem solution{M : ℕ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h : ∀ R ⊆ positions M, R.Nonempty → mass R w ≠ 0 →
      rbar R scanCost w = cellCentre R scanCost) :
    ∀ i ∈ positions M, ∀ j ∈ positions M, w i = w j := by
  intro i hi j hj
  rcases eq_or_ne i j with rfl | hij
  · rfl
  by_cases hmass : w i + w j = 0
  · have hi0 : w i = 0 := le_antisymm (by linarith [hw j]) (hw i)
    have hj0 : w j = 0 := le_antisymm (by linarith [hw i]) (hw j)
    rw [hi0, hj0]
  · have hsub : ({i, j} : Finset ℕ) ⊆ positions M := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hne : ({i, j} : Finset ℕ).Nonempty := ⟨i, by simp⟩
    have hm : mass ({i, j} : Finset ℕ) w = w i + w j := by
      simp [mass, Finset.sum_pair hij]
    have hmne : mass ({i, j} : Finset ℕ) w ≠ 0 := by rw [hm]; exact hmass
    have hkey := h {i, j} hsub hne hmne
    have hcard : (({i, j} : Finset ℕ).card : ℝ) = 2 := by
      rw [Finset.card_pair hij]; norm_num
    rw [rbar, hm, cellCentre, hcard, Finset.sum_pair hij, Finset.sum_pair hij] at hkey
    simp only [scanCost] at hkey
    have h2 : ((i : ℝ) * w i + (j : ℝ) * w j) * 2 = ((i : ℝ) + j) * (w i + w j) := by
      field_simp at hkey
      linarith [hkey]
    have hij' : (i : ℝ) ≠ (j : ℝ) := by exact_mod_cast hij
    have hz : ((i : ℝ) - j) * (w i - w j) = 0 := by nlinarith [h2]
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact absurd (by linarith : (i : ℝ) = j) hij'
    · linarith
