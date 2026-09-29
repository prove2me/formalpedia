-- Prove2me | solution 1 for mme_hash_extraction_cofinal_rate_of_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:46:18.280187+00:00
-- url     : https://prove2.me/submissions/6eddbd73-886d-440e-8cfd-898d05d59976

import Definitions.Def_mme_hash_extraction_certificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MME MME.HashExtraction Filter
open scoped BigOperators Topology
set_option autoImplicit false

/-- A copy exponent and a weighted-volume exponent retain the exact floor loss. -/
theorem mme_hash_extraction_rate_of_log_bounds
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

#print axioms mme_hash_extraction_rate_of_log_bounds

/-- Linear logarithmic bounds give a cofinal rate with an explicit vanishing loss. -/
theorem solution
    (D : ℕ → Data) (tau c w : ℝ) (hc : 0 < c)
    (hgap : 6 * Real.log 2401 < c + w)
    (hpower : Tendsto (fun n ↦ (D n).power) atTop atTop)
    (hdata : ∀ᶠ n in atTop,
      (∀ j, 0 < ((D n).hash j).lower) ∧
      0 < (D n).a * (D n).b * (D n).c ∧
      c * (D n).power ≤
        (∑ j, Real.log ((D n).hash j).lower) - Real.log (D n).repairCopies ∧
      w * (D n).power ≤ tau * Real.log (((D n).a * (D n).b * (D n).c : ℕ) : ℝ)) :
    ∃ V : ℝ, 2401 < V ∧
      Tendsto (fun n ↦ Real.exp (-(c * (D n).power))) atTop (nhds 0) ∧
      ∀ᶠ n in atTop,
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - Real.exp (-(c * (D n).power))) ≤
          (D n).rate tau := by
  refine ⟨Real.exp ((c + w) / 6), ?_, ?_, ?_⟩
  · apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2401)).1
    linarith
  · have hp : Tendsto (fun n ↦ ((D n).power : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hpower
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hp.const_mul_atTop hc))
  · filter_upwards [hdata] with n hn
    obtain ⟨hlower, hvolume, hcopies, hweight⟩ := hn
    have h := mme_hash_extraction_rate_of_log_bounds (D n) tau
      (c * (D n).power) (w * (D n).power)
      (mul_nonneg hc.le (Nat.cast_nonneg _)) hlower hvolume hcopies hweight
    have he : (Real.exp ((c + w) / 6) ^ (6 : ℕ)) ^ (D n).power =
        Real.exp (c * (D n).power + w * (D n).power) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [he]

#print axioms solution
