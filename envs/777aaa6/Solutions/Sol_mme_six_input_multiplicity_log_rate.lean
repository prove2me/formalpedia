-- Prove2me | solution 1 for mme_six_input_multiplicity_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:12.097681+00:00
-- url     : https://prove2.me/submissions/738bb6e7-854f-4553-b159-636fc5e7ca51

import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators
set_option autoImplicit false

/-- The sixth-power input multiplicity contributes exactly the sum of the six
logarithmic copy terms in the released extraction estimate. -/
theorem solution
    (inputs : Fin 6 → ℕ) (hinputs : ∀ owner, 1 ≤ inputs owner)
    (base : Fin 6 → ℝ) :
    Real.exp (∑ owner, (base owner + 6 * Real.log (inputs owner : ℝ))) =
      ((∏ owner, inputs owner ^ 6 : ℕ) : ℝ) * Real.exp (∑ owner, base owner) := by
  have hpos : ∀ owner, 0 < (inputs owner : ℝ) := by
    intro owner
    exact_mod_cast hinputs owner
  have hlog : Real.log ((∏ owner, inputs owner ^ 6 : ℕ) : ℝ) =
      ∑ owner, 6 * Real.log (inputs owner : ℝ) := by
    simp only [Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun owner _ => pow_ne_zero _ (hpos owner).ne')]
    simp only [Real.log_pow, Nat.cast_ofNat]
  rw [Finset.sum_add_distrib, ← hlog, Real.exp_add, Real.exp_log]
  · exact mul_comm _ _
  · exact_mod_cast Finset.prod_pos (fun owner _ => pow_pos (hinputs owner) _)


#print axioms solution
