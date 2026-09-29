-- Prove2me | solution 1 for PositionalStratum.bookedEC_of_uniform_cells
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:53:39.481421+00:00
-- url     : https://prove2.me/submissions/12cad49d-976d-4e1c-99a0-b456f5250eba

-- Sol generated from Applications/PositionalStratumEnvelope.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumEnvelope
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_mem_positions
import Theorems.Thm_PositionalStratum_sum_positions
/-
# The booked envelope : the sharp replacement for the failed value law

`Applications.PositionalStratumMeasure.value_universality_fails` shows that the booked
(uniform-within-cell) *value* law is not an upper bound once the weight is allowed to be
non-uniform inside the strata.  This file supplies the guarded version that survives:
a **two-sided envelope** determined by the bookings `(m, M, P)` alone, which is

* valid for *every* weight honouring the bookings (`EC_envelope`),
* **sharp** at both ends (`headWitness_attains_lower`, `tailWitness_attains_upper`), and
* contains the booked value (`bookedEC_mem_envelope`), which is therefore admissible as a
  *reporting* convention but not as a guarantee.

The file also records the F1 reporting convention itself: the positional-stratum law stated
with bookings, `EC = P·Θ_R·centre(R) + (1-P)·Θ_C·centre(C)` (`booked_law_theta_form`) — an
exact identity, never a bare `(μ,P)` closed form.
-/

open PositionalStratum

open Finset

noncomputable section

/-! ## Bounding a stratum's cost contribution by its mass -/



lemma positions_subset {m M : ℕ} (h : m ≤ M) : positions m ⊆ positions M := by
  intro i hi
  rw [mem_positions] at hi ⊢
  omega

/-! ## The booked envelope -/










/-! ## Exactness at uniform cells : where the booked law is the truth -/


/-! ## The F1 reporting convention : the law with bookings -/




open PositionalStratum in
theorem solution{M m : ℕ} {P : ℝ} {w : ℕ → ℝ} (hm : 0 < m) (hmM : m < M)
    (hR : ∀ i ∈ positions m, w i = P / m)
    (hC : ∀ i ∈ positions M \ positions m, w i = (1 - P) / ((M : ℝ) - m)) :
    EC M scanCost w = bookedEC M m P := by
  have hsub := positions_subset hmM.le
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hMm : (0 : ℝ) < (M : ℝ) - m := by
    have : (m : ℝ) < (M : ℝ) := by exact_mod_cast hmM
    linarith
  have hsplit : (∑ i ∈ positions M \ positions m, scanCost i * w i)
      + ∑ i ∈ positions m, scanCost i * w i = EC M scanCost w := Finset.sum_sdiff hsub
  have hcostsplit : (∑ i ∈ positions M \ positions m, scanCost i)
      + ∑ i ∈ positions m, scanCost i = ∑ i ∈ positions M, scanCost i := Finset.sum_sdiff hsub
  have hsumR : ∑ i ∈ positions m, scanCost i = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    simpa [scanCost] using sum_positions m
  have hsumM : ∑ i ∈ positions M, scanCost i = (M : ℝ) * ((M : ℝ) + 1) / 2 := by
    simpa [scanCost] using sum_positions M
  have hheadsum : ∑ i ∈ positions m, scanCost i * w i = P * ((m : ℝ) + 1) / 2 := by
    have : ∑ i ∈ positions m, scanCost i * w i
        = (∑ i ∈ positions m, scanCost i) * (P / m) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by rw [hR i hi]
    rw [this, hsumR]
    field_simp
  have htailsum : ∑ i ∈ positions M \ positions m, scanCost i * w i
      = (1 - P) * ((M : ℝ) + m + 1) / 2 := by
    have hval : ∑ i ∈ positions M \ positions m, scanCost i * w i
        = (∑ i ∈ positions M \ positions m, scanCost i) * ((1 - P) / ((M : ℝ) - m)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by rw [hC i hi]
    have hcost : ∑ i ∈ positions M \ positions m, scanCost i
        = (M : ℝ) * ((M : ℝ) + 1) / 2 - (m : ℝ) * ((m : ℝ) + 1) / 2 := by
      have := hcostsplit
      rw [hsumR, hsumM] at this
      linarith
    rw [hval, hcost]
    field_simp
    ring
  rw [← hsplit, hheadsum, htailsum, bookedEC]
  ring
