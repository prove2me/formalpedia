-- Prove2me | solution 1 for mme_CW_empty_cell_six_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:37:13.276465+00:00
-- url     : https://prove2.me/submissions/a9cdc511-9734-48f1-a870-d4b73fda8bb1

import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_rank_bridge

open MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
universe u

/-- An exact CW cell with no positions and zero marginal counts contributes
one scalar matrix tensor after full symmetrization. -/
theorem solution
    {K : Type u} [Field K] (q ell : ℕ) (shape : Fin 3 → ℕ) :
    Restrict (MMObj K 1 1 1)
      (sixSymmetrization (unbroken K q ell 0 (Equiv.refl _)
        (fun _ => Unit.unit) (fun _ => shape) (fun _ _ _ => 0))) := by
  classical
  have hfull : Restrict (source K q ell 0)
      (unbroken K q ell 0 (Equiv.refl _)
        (fun _ => Unit.unit) (fun _ => shape) (fun _ _ _ => 0)) := by
    apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
      (source K q ell 0) (source K q ell 0) (basis K q ell 0) _
      (fun _ => LinearMap.id)
    · simp
    · intro i x hx
      exfalso
      apply hx
      constructor
      · intro p
        exact Fin.elim0 p
      · simp [Useful, count]
  have hone : Isomorphic (MMObj K 1 1 1)
      (sixSymmetrization (source K q ell 0)) := by
    rw [← TensorQ.toQ_eq_iff]
    change MMq K 1 1 1 = _
    rw [MMq_one]
    simp only [source, Nat.zero_mul, kronPow, sixSymmetrization,
      cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
      ← TensorQ.permAut_toQ, ← TensorQ.toQ_one, map_one, one_mul]
  exact hone.1.trans (mme_sixSymmetrization_restrict hfull)


#print axioms solution
