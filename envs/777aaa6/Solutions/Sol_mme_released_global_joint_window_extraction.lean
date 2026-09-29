-- Prove2me | solution 1 for mme_released_global_joint_window_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:15:26.757222+00:00
-- url     : https://prove2.me/submissions/5eef2a8b-f7f3-44de-aef9-d4e9c0f6dc52

import Definitions.Def_mme_released_global_joint_interface
import Theorems.Thm_mme_global_CW_part_extraction
import Theorems.Thm_mme_regional_copied_restrictions_product_general
import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_profiled_CW_joint_projection_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.ReleasedGlobal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem solution {K : Type u} [Field K] (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (S : ∀ o, Part (4 * blocks k) 3 (physicalWindow o k hk (a o) (eps o))) :
    ∃ outputs : ℕ, Real.exp (∑ o, (S o).rate) ≤ (outputs : ℝ) ∧
      Restrict (bigAdd (fun _ : Fin outputs ↦ tensor K (jointWindow k hk a eps)))
        (bigAdd (fun _ : Fin (∏ o, (S o).inputs) ↦
          (CWObj K 5).kronPow (4 * (6 * blocks k)))) := by
  classical
  let M := 4 * (6 * blocks k)
  let copies : Fin 6 → ℕ := fun o ↦ ⌈Real.exp (S o).rate⌉₊
  have hp : Restrict (tensor K (fun _ (_ : FineWord M) ↦ True)) (raw K M) :=
    ⟨fun i ↦ ((raw K M).basisAllAllowedGrading (canonical K M)
      (fun _ _ ↦ True)).blockProj i 0, rfl⟩
  have hgroup : Restrict (kronFin 6 (fun _ : Fin 6 ↦
      tensor K (fun _ (_ : FineWord (4 * blocks k)) ↦ True))) (raw K M) :=
    (mme_profiled_CW_region_product_restrict (fun _ (_ : FineWord M) ↦ True)
      (fun _ : Fin 6 ↦ 4 * blocks k) (jointPositions k)
      (fun _ _ (_ : FineWord (4 * blocks k)) ↦ True)
      (fun _ _ _ ↦ trivial)).trans hp
  have hparts := mme_regional_copied_restrictions_product_general (raw K M)
    (fun _ : Fin 6 ↦ tensor K (fun _ (_ : FineWord (4 * blocks k)) ↦ True))
    (fun o ↦ tensor K (physicalWindow o k hk (a o) (eps o)))
    (fun o ↦ (S o).inputs) copies hgroup
    (fun o ↦ mme_global_CW_part_extraction (S o))
  have hproject := mme_profiled_CW_joint_projection_restrict (K := K)
    (fun _ : Fin 6 ↦ 4 * blocks k) (jointPositions k)
    (fun o ↦ physicalWindow o k hk (a o) (eps o))
    (jointWindow k hk a eps) (fun _ _ h ↦ h)
  refine ⟨∏ o, copies o, ?_,
    (mme_bigAdd_mono_restrict (fun _ : Fin (∏ o, copies o) ↦ hproject)).trans hparts⟩
  simp only [Real.exp_sum,Nat.cast_prod]
  exact Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le)
    (fun o _ ↦ Nat.le_ceil (Real.exp (S o).rate))
