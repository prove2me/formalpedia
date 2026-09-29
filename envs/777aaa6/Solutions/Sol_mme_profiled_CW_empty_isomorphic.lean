-- Prove2me | solution 1 for mme_profiled_CW_empty_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:36.804264+00:00
-- url     : https://prove2.me/submissions/d628b3d4-7e56-409a-9889-44595c464fcd

import Theorems.Thm_mme_profiled_CW_tensor_restrict_power
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_rank_bridge

open MME MME.TensorObj MME.ProfiledCW
universe u

/-- An unrestricted profile on zero elementary positions is the scalar tensor,
with mutual restrictions before any symmetrization. -/
theorem solution
    {K : Type u} [Field K] {N : ℕ} (hN : N = 0)
    (P : Predicate N) (hp : ∀ i x, P i x) :
    Isomorphic (tensor K P) oneObj := by
  subst N
  classical
  have hfull : Restrict (raw K 0) (tensor K P) := by
    apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
      (raw K 0) (raw K 0) (canonical K 0) _ (fun _ => LinearMap.id)
    · simp
    · intro i x hx
      exact (hx (hp i (fine x))).elim
  have hone : Isomorphic (raw K 0) (oneObj : TensorObj K 3) := by
    rw [← TensorQ.toQ_eq_iff]
    rfl
  exact ⟨(mme_profiled_CW_tensor_restrict_power P).trans hone.1,
    hone.2.trans hfull⟩


#print axioms solution
