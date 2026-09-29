-- Prove2me | solution 1 for mme_sixSymmetrization_repeated_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:11.224234+00:00
-- url     : https://prove2.me/submissions/222eaef1-e90d-41f4-83d8-b3ffeaee82ab

import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators
universe u
set_option autoImplicit false

/-- Repeating a tensor before six-symmetrization gives the sixth power of
its multiplicity, with no loss of copies. -/
theorem solution
    {K : Type u} [Field K] (p : ℕ) (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin (p ^ 6) => sixSymmetrization T))
      (sixSymmetrization (TensorObj.bigAdd (fun _ : Fin p => T))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.toQ_bigAdd, ← TensorQ.permAut_toQ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    map_mul, map_natCast, Nat.cast_pow]
  ring



#print axioms solution
