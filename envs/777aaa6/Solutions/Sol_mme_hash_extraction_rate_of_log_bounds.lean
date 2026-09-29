-- Prove2me | solution 1 for mme_hash_extraction_rate_of_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:46:17.482885+00:00
-- url     : https://prove2.me/submissions/deb3ebd2-5da5-4c08-815a-eeca874d480d

import Definitions.Def_mme_hash_extraction_certificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MME MME.HashExtraction Filter
open scoped BigOperators Topology
set_option autoImplicit false

/-- A copy exponent and a weighted-volume exponent retain the exact floor loss. -/
theorem solution
    (D : Data) (tau c w : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ j, 0 < (D.hash j).lower)
    (hvolume : 0 < D.a * D.b * D.c)
    (hcopies : c ≤ (∑ j, Real.log (D.hash j).lower) - Real.log D.repairCopies)
    (hweight : w ≤ tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ)) :
    Real.exp (c + w) * (1 - Real.exp (-c)) ≤ D.rate tau := by
  have hprod : 0 < ∏ j, (D.hash j).lower := Finset.prod_pos (fun j _ ↦ hlower j)
  have hrepair : (0 : ℝ) < D.repairCopies := by exact_mod_cast D.repair_pos
  have hv : (0 : ℝ) < (D.a * D.b * D.c : ℕ) := by exact_mod_cast hvolume
  have hlog : Real.log ((∏ j, (D.hash j).lower) / D.repairCopies) =
      (∑ j, Real.log (D.hash j).lower) - Real.log D.repairCopies := by
    rw [Real.log_div hprod.ne' hrepair.ne', Real.log_prod (fun j _ ↦ (hlower j).ne')]
  have hcopy : Real.exp c ≤ (∏ j, (D.hash j).lower) / D.repairCopies := by
    apply (Real.le_log_iff_exp_le (div_pos hprod hrepair)).1
    rwa [hlog]
  have hw : Real.exp w ≤ ((D.a * D.b * D.c : ℕ) : ℝ) ^ tau := by
    rw [Real.rpow_def_of_pos hv]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hweight)
  have hnonneg : 0 ≤ Real.exp c - 1 := by
    have := Real.one_le_exp_iff.mpr hc
    linarith
  have hid : Real.exp (c + w) * (1 - Real.exp (-c)) =
      (Real.exp c - 1) * Real.exp w := by
    rw [Real.exp_add, Real.exp_neg]
    field_simp
  rw [hid, Data.rate]
  exact mul_le_mul (by linarith) hw (Real.exp_pos w).le (by linarith)

#print axioms solution

