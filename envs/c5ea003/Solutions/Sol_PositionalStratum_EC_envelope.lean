-- Prove2me | solution 1 for PositionalStratum.EC_envelope
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:51:32.523821+00:00
-- url     : https://prove2.me/submissions/68e67bef-ee0f-46fa-8ea3-2c06f75d976d

-- Sol generated from Applications/PositionalStratumEnvelope.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumEnvelope
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_mass_compl
import Theorems.Thm_PositionalStratum_mem_positions
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

lemma sum_cost_lower {S : Finset ℕ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {lo : ℝ}
    (hlo : ∀ i ∈ S, lo ≤ (i : ℝ)) :
    lo * mass S w ≤ ∑ i ∈ S, scanCost i * w i := by
  rw [mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hlo i hi) (hw i)

lemma sum_cost_upper {S : Finset ℕ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {hi : ℝ}
    (hhi : ∀ i ∈ S, (i : ℝ) ≤ hi) :
    ∑ i ∈ S, scanCost i * w i ≤ hi * mass S w := by
  rw [mass, Finset.mul_sum]
  exact Finset.sum_le_sum fun i h => mul_le_mul_of_nonneg_right (hhi i h) (hw i)

lemma positions_subset {m M : ℕ} (h : m ≤ M) : positions m ⊆ positions M := by
  intro i hi
  rw [mem_positions] at hi ⊢
  omega

/-! ## The booked envelope -/










/-! ## Exactness at uniform cells : where the booked law is the truth -/


/-! ## The F1 reporting convention : the law with bookings -/




open PositionalStratum in
theorem solution{M m : ℕ} {w : ℕ → ℝ} {P : ℝ} (hmM : m ≤ M)
    (hw : ∀ i, 0 ≤ w i) (hhead : mass (positions m) w = P)
    (htot : mass (positions M) w = 1) :
    P * 1 + (1 - P) * ((m : ℝ) + 1) ≤ EC M scanCost w ∧
      EC M scanCost w ≤ P * m + (1 - P) * M := by
  have hsub := positions_subset hmM
  have hsplit : (∑ i ∈ positions M \ positions m, scanCost i * w i)
      + ∑ i ∈ positions m, scanCost i * w i = EC M scanCost w := Finset.sum_sdiff hsub
  have htail : mass (positions M \ positions m) w = 1 - P := by
    rw [mass_compl hsub htot, hhead]
  -- head bounds
  have hh1 : (1 : ℝ) * mass (positions m) w ≤ ∑ i ∈ positions m, scanCost i * w i :=
    sum_cost_lower hw (fun i hi => by
      have := (mem_positions.mp hi).1
      exact_mod_cast this)
  have hh2 : ∑ i ∈ positions m, scanCost i * w i ≤ (m : ℝ) * mass (positions m) w :=
    sum_cost_upper hw (fun i hi => by
      have := (mem_positions.mp hi).2
      exact_mod_cast this)
  -- tail bounds
  have htmem : ∀ i ∈ positions M \ positions m, m + 1 ≤ i ∧ i ≤ M := by
    intro i hi
    rw [Finset.mem_sdiff, mem_positions, mem_positions] at hi
    omega
  have ht1 : ((m : ℝ) + 1) * mass (positions M \ positions m) w
      ≤ ∑ i ∈ positions M \ positions m, scanCost i * w i :=
    sum_cost_lower hw (fun i hi => by
      have := (htmem i hi).1
      have : ((m : ℕ) + 1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast this
      linarith)
  have ht2 : ∑ i ∈ positions M \ positions m, scanCost i * w i
      ≤ (M : ℝ) * mass (positions M \ positions m) w :=
    sum_cost_upper hw (fun i hi => by
      have := (htmem i hi).2
      exact_mod_cast this)
  rw [hhead] at hh1 hh2
  rw [htail] at ht1 ht2
  constructor
  · linarith [hsplit, hh1, ht1]
  · linarith [hsplit, hh2, ht2]
