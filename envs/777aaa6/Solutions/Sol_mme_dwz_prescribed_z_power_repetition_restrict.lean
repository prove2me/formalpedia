-- Prove2me | solution 1 for mme_dwz_prescribed_z_power_repetition_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:50:02.517975+00:00
-- url     : https://prove2.me/submissions/c951405b-d9e9-4033-9411-a0501244df92

import Theorems.Thm_mme_dwz_prescribed_z_power_concatenation_restrict
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Definitions.Def_mme_tensor_bridge

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem unit_restrict_prescribed_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) :
    TensorObj.Restrict (TensorObj.oneObj : TensorObj K 3)
      (prescribedZPower T bZ grade p 0) := by
  classical
  unfold prescribedZPower prescribedZWord
  simp only [IntegerZSplitProfile.length, Nat.mul_zero]
  refine @mme_restrict_basisZAllowedSubtensor_of_vanishes K _
    (T.kronPow 0) TensorObj.oneObj (PowIndex ι 0)
    (kronPowModeBasis T 2 bZ 0)
    (fun w ↦ ∀ a, leftGradeCount grade w a = 0)
    (fun _ ↦ Classical.propDecidable _)
    (fun _ ↦ LinearMap.id) ?_ ?_
  · exact LinearMap.congr_fun (PiTensorProduct.map_id (R := K)) _
  · intro w hnot
    exfalso
    apply hnot
    intro a
    simp [leftGradeCount]

private theorem repeat_from_concatenation
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t)
    (hconcat : ∀ m n : ℕ, TensorObj.Restrict
      (TensorObj.kron (prescribedZPower T bZ grade p m)
        (prescribedZPower T bZ grade p n))
      (prescribedZPower T bZ grade p (m + n))) (m r : ℕ) :
    TensorObj.Restrict ((prescribedZPower T bZ grade p m).kronPow r)
      (prescribedZPower T bZ grade p (m * r)) := by
  induction r with
  | zero =>
    simpa only [Nat.mul_zero] using unit_restrict_prescribed_zero T bZ grade p
  | succ r ih =>
    have hstep : TensorObj.Restrict
        (TensorObj.kron (prescribedZPower T bZ grade p m)
          ((prescribedZPower T bZ grade p m).kronPow r))
        (TensorObj.kron (prescribedZPower T bZ grade p m)
          (prescribedZPower T bZ grade p (m * r))) := by
      let P := tensorPreorder K
      change P.le
        (TensorQ.toQ (prescribedZPower T bZ grade p m) *
          TensorQ.toQ ((prescribedZPower T bZ grade p m).kronPow r))
        (TensorQ.toQ (prescribedZPower T bZ grade p m) *
          TensorQ.toQ (prescribedZPower T bZ grade p (m * r)))
      simpa only [mul_comm] using
        P.mul_right
          (TensorQ.toQ ((prescribedZPower T bZ grade p m).kronPow r))
          (TensorQ.toQ (prescribedZPower T bZ grade p (m * r))) ih
          (TensorQ.toQ (prescribedZPower T bZ grade p m))
    simpa only [Nat.mul_succ, Nat.add_comm] using
      hstep.trans (hconcat m (m * r))

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m r : ℕ) :
    TensorObj.Restrict ((prescribedZPower T bZ grade p m).kronPow r)
      (prescribedZPower T bZ grade p (m * r)) := by
  exact repeat_from_concatenation T bZ grade p
    (mme_dwz_prescribed_z_power_concatenation_restrict T bZ grade p) m r
