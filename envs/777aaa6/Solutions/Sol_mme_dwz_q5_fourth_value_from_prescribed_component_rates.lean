-- Prove2me | solution 1 for mme_dwz_q5_fourth_value_from_prescribed_component_rates
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T17:36:10.511283+00:00
-- url     : https://prove2.me/submissions/4c4c1147-7003-46d5-bd23-bc7f91984b0c

import Theorems.Thm_mme_dwz_q5_global_node_weighted_assembly
import Theorems.Thm_mme_dwz_prescribed_z_weighted_node_finite_closure_from_length
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades
import Theorems.Thm_mme_kronPow_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_dwz_prescribed_z_power_projection
import Mathlib.Tactic

open MME MME.TensorObj MME.StothersFourth MME.DWZRestrictedValue
open MME.CompleteSplit.CWFourth MME.DWZQ5ExactData
open MME.DWZFourthGlobalWitness MME.DWZQ5AsymptoticData
open BigOperators Module Filter
open scoped Classical
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

namespace MME.Global45Assembly

attribute [local irreducible] D scale component rawProfile rawCount rawDenominator
  coarseAddress

def parentProfile : IntegerZSplitProfile 1 where
  denominator := 4
  denominator_pos := by norm_num
  count := fun _ => 4
  count_sum := by simp

theorem inverse_restrict {K : Type u} [Field K] (X Y : TensorObj K 3)
    (f : ∀ i, X.V i ≃ₗ[K] Y.V i)
    (h : PiTensorProduct.map (fun i => (f i).toLinearMap) X.t = Y.t) :
    TensorObj.Restrict X Y := by
  refine ⟨fun i => (f i).symm.toLinearMap, ?_⟩
  have hc := congrArg (PiTensorProduct.map (fun i => (f i).symm.toLinearMap)) h
  have hi : PiTensorProduct.map (fun i => (f i).symm.toLinearMap)
      (PiTensorProduct.map (fun i => (f i).toLinearMap) X.t) = X.t := by
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp only [LinearEquiv.symm_comp, PiTensorProduct.map_id, LinearMap.id_apply]
  exact hc.symm.trans hi

theorem fourth_restrict {K : Type u} [Field K] :
    TensorObj.Restrict ((CWObj K 5).kronPow 4) (cwFourthObj K 5) := by
  obtain ⟨f, hf, _⟩ :=
    mme_CW_fourth_balanced_linear_equiv_preserves_basis_and_grades (K := K) 5
  exact inverse_restrict _ _ f hf

theorem fourth_value_of_parent_sequence {K : Type u} [Field K]
    {ι : Type u} (b : Basis ι K ((CWObj K 5).V 2))
    (tau S R : ℝ) (hSR : S < R)
    (h : HasPrescribedZSixRestrictionValueAtLeast (CWObj K 5)
      b (fun _ => (0 : Fin 1)) parentProfile tau (Real.exp (R / 4))) :
    HasSixSymmetricTauValueAtLeast (cwFourthObj K 5) tau (Real.exp S) := by
  refine ⟨by positivity, ?_⟩
  intro epsilon hepsilon
  apply Filter.frequently_atTop.2
  intro cutoff
  obtain ⟨m, hm, _, k, a, b', c, hrest, hsize⟩ :=
    h.2 (Real.exp (S / 4)) (Real.exp_pos _) (Real.exp_lt_exp.mpr (by linarith)) cutoff
  have hsource : TensorObj.Restrict
      (prescribedZPower (CWObj K 5) b (fun _ => (0 : Fin 1)) parentProfile m)
      ((cwFourthObj K 5).kronPow m) := by
    have hp := mme_dwz_prescribed_z_power_projection
      (CWObj K 5) b (fun _ => (0 : Fin 1)) parentProfile m
    have hnest := (mme_kronPow_kronPow_isomorphic (CWObj K 5) 4 m).2
    have hf := mme_restrict_kronPow (fourth_restrict (K := K)) m
    apply TensorObj.Restrict.trans hp
    apply TensorObj.Restrict.trans ?_ hf
    simpa only [IntegerZSplitProfile.length, parentProfile, Nat.mul_comm] using hnest
  have htarget := TensorObj.Restrict.trans hrest (mme_sixSymmetrization_restrict hsource)
  have hfinal := TensorObj.Restrict.trans htarget
    (mme_sixSymmetrization_kronPow_isomorphic (cwFourthObj K 5) m).2
  refine ⟨m, hm, k, a, b', c, hfinal, ?_⟩
  have heq : Real.exp (S / 4) ^ (6 * parentProfile.length m) =
      (Real.exp S ^ 6) ^ m := by
    simp only [IntegerZSplitProfile.length, parentProfile, ← Real.exp_nat_mul,
      Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    ring
  rw [heq] at hsize
  exact (mul_le_of_le_one_right (by positivity) (by linarith)).trans hsize

noncomputable def averageRate (x : Fin 45 → ℝ) : ℝ :=
  (∑ c, (component c : ℝ) * x c) / (scale : ℝ)

theorem global_value_of_component_rates {K : Type u} [Field K]
    (tau rho S : ℝ) (x : Fin 45 → ℝ)
    (hrho : 0 ≤ rho) (hgap : rho < extractionRate)
    (hS : S < rho + averageRate x)
    (hvalue : ∀ c : Fin 45, HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
      (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) =>
        cwSquarePairGrade 5 a.down.val.1)
      (rawProfile c) tau (Real.exp (x c))) :
    HasSixSymmetricTauValueAtLeast (cwFourthObj K 5) tau (Real.exp S) := by
  classical
  have hs : (0 : ℝ) < scale := by
    exact_mod_cast mme_dwz_q5_exact_global_profile_certificate.1
  have hd : 0 < D := by
    unfold D
    exact Finset.prod_pos (fun c _ => (rawProfile c).denominator_pos)
  have hsum : (∑ c : Fin 45, (component c : ℝ)) = scale := by
    exact_mod_cast mme_dwz_q5_exact_global_profile_certificate.2.2.1
  let delta : ℝ := (rho + averageRate x - S) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  let R : ℝ := rho + averageRate x - delta
  have hSR : S < R := by dsimp [R, delta]; linarith
  let v : Fin 45 → ℝ := fun c => Real.exp (x c - delta)
  let b := Module.Free.chooseBasis K ((CWObj K 5).V 2)
  obtain ⟨threshold, ha⟩ := mme_dwz_q5_global_node_weighted_assembly
    b parentProfile rfl rho hrho hgap tau v (fun c => Real.exp_pos _) 1 (by norm_num)
  have hw : (∑ c, (component c : ℝ) * (x c - delta)) =
      (scale : ℝ) * (averageRate x - delta) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, averageRate]
    field_simp
  have heq : Real.exp (R / 4) ^ (4 * (scale * D * 1)) =
      Real.exp (rho / 4) ^ (4 * (scale * D * 1)) *
        ∏ c, v c ^ (component c * D * 1) := by
    simp only [v, ← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one]
    congr 1
    have hprod : (∑ c, (component c : ℝ) * (D : ℝ) * (x c - delta)) =
        (D : ℝ) * ((scale : ℝ) * (averageRate x - delta)) := by
      rw [← hw, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hprod]
    dsimp [R]
    ring
  have hp := mme_dwz_prescribed_z_weighted_node_finite_closure_from_length
    (CWObj K 5) _ b (fun _ => (0 : Fin 1)) parentProfile _ _
    (fun c => rawProfile c) (fun c => component c * D * 1)
    (4 * (scale * D * 1)) threshold tau (Real.exp (rho / 4))
    (fun c => Real.exp (x c)) v (Real.exp (R / 4))
    (by positivity) (by positivity)
    (Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.mul_pos
      mme_dwz_q5_exact_global_profile_certificate.1 hd) (by norm_num)))
    heq.le (fun c => Real.exp_pos _)
    (fun c => Real.exp_lt_exp.mpr (sub_lt_self _ hdelta)) hvalue ha
  exact fourth_value_of_parent_sequence b tau S R hSR hp

end MME.Global45Assembly

theorem solution {K : Type u} [Field K]
    (tau rho S : ℝ) (x : Fin 45 → ℝ)
    (hrho : 0 ≤ rho) (hgap : rho < extractionRate)
    (hS : S < rho + (∑ c, (component c : ℝ) * x c) / (scale : ℝ))
    (hvalue : ∀ c : Fin 45, HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
      (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
      (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) =>
        cwSquarePairGrade 5 a.down.val.1)
      (rawProfile c) tau (Real.exp (x c))) :
    HasSixSymmetricTauValueAtLeast (cwFourthObj K 5) tau (Real.exp S) := by
  exact MME.Global45Assembly.global_value_of_component_rates tau rho S x hrho hgap hS hvalue
