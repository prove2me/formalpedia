-- Prove2me | solution 2 for mme_dwz_q6_121_211_common_halving_family_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T06:00:37.229491+00:00
-- url     : https://prove2.me/submissions/95ebf939-a74e-412d-8715-7482af5fb494

import Theorems.Thm_mme_dwz_q6_common_halving_shared_Z_star_source_restriction
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
import Theorems.Thm_mme_coupled_four_block_exact_address_component_certificate
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open MME MME.DWZComponentRestriction MME.CompleteSplit112
open CoupledCTensorPackaging Module
open scoped BigOperators
universe u
set_option autoImplicit false

private theorem behrend_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    Real.exp (-200 * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  apply Real.exp_le_exp.mpr
  linarith


theorem solution
    {K : Type u} [Field K]
    (tau : ℝ)
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hHbound : H ≤ 4 ^ (MME.DWZTable2Counts.component s * m)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau) *
          Real.exp (-200 * Real.sqrt
            ((((MME.DWZTable2Counts.component s * m) + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)  := by
  classical
  let N := DWZTable2Counts.component s * m
  let S := TensorObj.bigAdd (starObj (grading K 6) family)
  have hcert (a : Fin A) : Nonempty
      (CTensorOneHOneCertificate (starObj (grading K 6) family a) H
        (6 ^ (4 * G + 2 * L))) := by
    obtain ⟨_, h000, h111, h012, h102⟩ :=
      mme_complete_split_112_concrete_four_block_certificate (K := K) 6
    have hc (h : Fin H) : ∃ x y z : ℕ,
        TensorObj.Isomorphic (MMObj K x y z)
          (componentObj (grading K 6) family a h) ∧
        x * y * z = 6 ^ (4 * G + 2 * L) :=
      mme_coupled_four_block_exact_address_component_certificate
        6 N L G (coupledObj K 6) (grading K 6) h000 h111 h012 h102
        (componentExactAddress family a h)
    choose x y z hiso hv using hc
    have hstar := mme_primary_hash_family_sharedZ_star_grading_components
      (grading K 6) family a
    exact ⟨{ grading := starGrading (grading K 6) family a
             supported := hstar.1
             m := x, n := y, p := z
             component := fun h => (hiso h).trans (hstar.2 h)
             common_volume := hv }⟩
  let cert : CTensorOneHOneFamilyCertificate S A H (6 ^ (4 * G + 2 * L)) :=
    { star := starObj (grading K 6) family
      restrict := TensorObj.Restrict.refl S
      certificate := fun a => (hcert a).some }
  obtain ⟨k, a, b, c, hr, hk, hv⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction cert family.hHpos
  refine ⟨k, a, b, c, hr.trans ?_, ?_⟩
  · exact mme_dwz_q6_common_halving_shared_Z_star_source_restriction
      (K := K) s hs m rfl family halving
  · let w : ℝ := (((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau
    have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    have hloss := behrend_loss_bound N H hHbound
    have hcount : (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
        Real.exp (-200 * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
      calc
        _ ≤ (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hloss (by positivity)
        _ ≤ (k : ℝ) := by simpa only [mul_assoc] using hk
    have hsum : (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) = (k : ℝ) * w := by
      simp only [hv]
      simp [w]
    rw [hsum]
    simpa only [w, N, Nat.cast_pow, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm]
      using mul_le_mul_of_nonneg_right hcount hw

#print axioms solution
