-- Prove2me | solution 1 for mme_joint_regional_CW_plan_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T00:58:25.857309+00:00
-- url     : https://prove2.me/submissions/3b58e7e8-6ccb-4032-baf4-1f4e15a84e49

import Definitions.Def_mme_recursive_regional_CW_data
import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_regional_copied_restrictions_product
import Theorems.Thm_mme_profiled_CW_mode_permutation_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_basis_projected_type_cover_restrict
import Theorems.Thm_mme_type_cover_uniform_copy_extraction
import Theorems.Thm_mme_batched_restrictions_compose
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_CW_three_canonical_support
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_joint_regional_CW_plan_data
import Theorems.Thm_mme_joint_regional_CW_part_stage_sound
import Theorems.Thm_mme_profiled_CW_joint_projection_restrict
import Theorems.Thm_mme_regional_copied_restrictions_product_general

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.DWZStep1Support MME.CompleteSplit Module PiTensorProduct TensorProduct
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

private theorem perm_sums' {K : Type u} [Field K] (sigma : Equiv.Perm (Fin 3))
    (T : TensorObj K 3) (n : ℕ) :
    Isomorphic (permObj sigma (bigAdd (fun _ : Fin n ↦ T)))
      (bigAdd (fun _ : Fin n ↦ permObj sigma T)) := by
  apply TensorQ.toQ_eq_iff.mp
  rw [← TensorQ.permAut_toQ, TensorQ.toQ_bigAdd, map_sum, TensorQ.toQ_bigAdd]
  simp only [TensorQ.permAut_toQ]


private theorem perm_extraction' {K : Type u} [Field K] {N : ℕ} (P : Predicate N)
    (sigma : Equiv.Perm (Fin 3)) (hsigma : sigma = cyclicPerm ∨ sigma = swapFirstTwoPerm)
    (inputs outputs a b c a' b' c' : ℕ)
    (hmm : Isomorphic (permObj sigma (MMObj K a b c)) (MMObj K a' b' c'))
    (h : TensorObj.Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K a b c))
      (bigAdd (fun _ : Fin inputs ↦ tensor K P))) :
    TensorObj.Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K a' b' c'))
      (bigAdd (fun _ : Fin inputs ↦ tensor K (fun i ↦ P (sigma.symm i)))) := by
  exact (mme_bigAdd_mono_restrict (fun _ : Fin outputs ↦ hmm.2)).trans
    ((perm_sums' sigma (MMObj K a b c) outputs).2.trans
      ((permObj_restrict sigma h).trans
        ((perm_sums' sigma (tensor K P) inputs).1.trans
          (mme_bigAdd_mono_restrict (fun _ : Fin inputs ↦
            (mme_profiled_CW_mode_permutation_iso P sigma hsigma).2)))))

/-- **Soundness of joint regional plans.** -/
theorem solution {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : JointPlan N ell P) :
    TensorObj.Restrict (bigAdd (fun _ : Fin D.outputs ↦ MMObj K D.a D.b D.c))
      (bigAdd (fun _ : Fin D.inputs ↦ tensor K P)) := by
  induction D with
  | base D => exact mme_recursive_regional_CW_plan_sound D
  | @stage N ell lower parts P Q hlevel size positions S T source steps target next ih =>
    have hgroup := mme_profiled_CW_region_product_restrict (K := K) P size positions S source
    have hprod := mme_regional_copied_restrictions_product_general (tensor K P) (fun j ↦ tensor K (S j))
      (fun j ↦ tensor K (T j)) (fun j ↦ (steps j).types) (fun j ↦ (steps j).copies) hgroup
      (fun j ↦ mme_joint_regional_CW_part_stage_sound (steps j))
    have hQ := mme_profiled_CW_joint_projection_restrict (K := K) size positions T Q target
    have hstep : TensorObj.Restrict (bigAdd (fun _ : Fin (∏ j, (steps j).copies) ↦ tensor K Q))
        (bigAdd (fun _ : Fin (∏ j, (steps j).types) ↦ tensor K P)) :=
      (mme_bigAdd_mono_restrict (fun _ ↦ hQ)).trans hprod
    exact mme_batched_restrictions_compose (tensor K P) (tensor K Q)
      (MMObj K next.a next.b next.c) (∏ j, (steps j).types) next.inputs
      (∏ j, (steps j).copies) next.outputs hstep ih
  | @partition N ell parts P size positions Q inside children ih =>
    exact mme_regional_copied_restrictions_product (tensor K P) (fun j ↦ tensor K (Q j))
      (fun j ↦ (children j).a) (fun j ↦ (children j).b) (fun j ↦ (children j).c)
      (fun j ↦ (children j).inputs) (fun j ↦ (children j).outputs)
      (mme_profiled_CW_region_product_restrict P size positions Q inside) ih
  | @rotate N ell P child ih =>
    exact perm_extraction' P cyclicPerm (Or.inl rfl) child.inputs child.outputs
      child.a child.b child.c child.c child.a child.b
      (MMObj_permObj_cyclic child.a child.b child.c) ih
  | @swap N ell P child ih =>
    exact perm_extraction' P swapFirstTwoPerm (Or.inr rfl) child.inputs child.outputs
      child.a child.b child.c child.c child.b child.a
      (mme_MMObj_permObj_swapFirstTwo child.a child.b child.c) ih
