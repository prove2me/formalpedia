-- Prove2me | solution 1 for mme_profiled_CW_empty_six_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:25:30.998429+00:00
-- url     : https://prove2.me/submissions/6b2b00fa-19ee-4ad6-b93b-dc5818af87df

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open MME MME.TensorObj MME.ProfiledCW
universe u

/-- An unrestricted profile on zero elementary positions contributes one
scalar matrix tensor after six symmetrization. -/
theorem solution
    {K : Type u} [Field K] {N : ℕ} (hN : N = 0)
    (P : Predicate N) (hp : ∀ i x, P i x) :
    Restrict (MMObj K 1 1 1) (sixSymmetrization (tensor K P)) := by
  subst N
  classical
  have hfull : Restrict (raw K 0) (tensor K P) := by
    apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
      (raw K 0) (raw K 0) (canonical K 0) _ (fun _ => LinearMap.id)
    · simp
    · intro i x hx
      exact (hx (hp i (fine x))).elim
  have hone : Isomorphic (MMObj K 1 1 1) (sixSymmetrization (raw K 0)) := by
    rw [← TensorQ.toQ_eq_iff]
    change MMq K 1 1 1 = _
    rw [MMq_one]
    simp only [raw, kronPow, sixSymmetrization,
      cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
      ← TensorQ.permAut_toQ, ← TensorQ.toQ_one, map_one, one_mul]
  exact hone.1.trans (mme_sixSymmetrization_restrict hfull)


#print axioms solution
