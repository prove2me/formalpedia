-- Prove2me | solution 1 for mme_global_CW_graded_start_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T15:51:51.188338+00:00
-- url     : https://prove2.me/submissions/23496ecd-2a62-4d07-b178-2ca095343178

import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_global_CW_part_extraction
import Theorems.Thm_mme_regional_copied_restrictions_product_general
import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_profiled_CW_joint_projection_restrict
import Theorems.Thm_mme_joint_regional_CW_plan_sound
import Theorems.Thm_mme_batched_restrictions_compose
import Theorems.Thm_mme_bigAdd_mono_restrict
import Definitions.Def_mme_global_CW_graded_start_data
import Theorems.Thm_mme_logarithmic_graded_joint_regional_recipe_compilation

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u

theorem solution {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.StartG M ell) :
    ∃ outputs : ℕ, Real.exp D.logOutputs ≤ (outputs : ℝ) ∧
      TensorObj.Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K D.a D.b D.c))
        (bigAdd (fun _ : Fin D.inputs ↦ (CWObj K 5).kronPow M)) := by
  classical
  let copies : Fin D.parts → ℕ := fun j ↦ ⌈Real.exp (D.steps j).rate⌉₊
  have hp : TensorObj.Restrict (tensor K (fun _ (_ : FineWord M) ↦ True)) (raw K M) :=
    ⟨fun i ↦ ((raw K M).basisAllAllowedGrading (canonical K M)
      (fun _ _ ↦ True)).blockProj i 0, rfl⟩
  have hgroup : TensorObj.Restrict (kronFin D.parts (fun j ↦
      tensor K (fun _ (_ : FineWord (D.size j)) ↦ True))) (raw K M) :=
    (mme_profiled_CW_region_product_restrict (fun _ (_ : FineWord M) ↦ True)
      D.size D.positions (fun j _ (_ : FineWord (D.size j)) ↦ True)
      (fun _ _ _ ↦ trivial)).trans hp
  have hparts := mme_regional_copied_restrictions_product_general (raw K M)
    (fun j ↦ tensor K (fun _ (_ : FineWord (D.size j)) ↦ True))
    (fun j ↦ tensor K (D.T j)) (fun j ↦ (D.steps j).inputs) copies hgroup
    (fun j ↦ mme_global_CW_part_extraction (D.steps j))
  have hproject := mme_profiled_CW_joint_projection_restrict (K := K) D.size D.positions D.T D.Q D.target
  have hglobal := (mme_bigAdd_mono_restrict (fun _ : Fin (∏ j, copies j) ↦ hproject)).trans hparts
  obtain ⟨A,hAi,hAo,hAd⟩ := mme_logarithmic_graded_joint_regional_recipe_compilation D.next
  have ha : A.a = D.a := congrArg (fun d : ℕ × ℕ × ℕ ↦ d.1) hAd
  have hb : A.b = D.b := congrArg (fun d : ℕ × ℕ × ℕ ↦ d.2.1) hAd
  have hc : A.c = D.c := congrArg (fun d : ℕ × ℕ × ℕ ↦ d.2.2) hAd
  have hnext := mme_joint_regional_CW_plan_sound (K := K) A
  rw [hAi,ha,hb,hc] at hnext
  have hfinal := mme_batched_restrictions_compose (raw K M) (tensor K D.Q)
    (MMObj K D.a D.b D.c) (∏ j, (D.steps j).inputs) D.next.inputs
    (∏ j, copies j) A.outputs hglobal hnext
  refine ⟨(∏ j, copies j) * A.outputs, ?_, hfinal⟩
  simp only [GlobalCW.StartG.logOutputs,Real.exp_add,Real.exp_sum,Nat.cast_mul,Nat.cast_prod]
  exact mul_le_mul
    (Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le)
      (fun j _ ↦ Nat.le_ceil (Real.exp (D.steps j).rate))) hAo
    (Real.exp_pos _).le (by positivity)

