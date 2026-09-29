-- Prove2me | solution 1 for mme_CWTensor_canonical_term_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:02:50.055289+00:00
-- url     : https://prove2.me/submissions/923c7c50-a228-4337-b3b2-b8098b0d735f

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_term_expansion

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    CWTensor K q =
      ∑ t : MME.StothersFourth.Phi116.CWTerm q,
        MME.StothersFourth.Phi116.cwTermMonom K q t := by
  have hM (i : Fin q) :
      (⟨i.val + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 = 1 + i.val
    omega
  have hT :
      (⟨q + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + q, by omega⟩ := by
    apply Fin.ext
    change q + 1 = 1 + q
    omega
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  unfold CWTensor MME.StothersFourth.Phi116.cwTermMonom
  simp [MME.StothersFourth.Phi116.cwTermTriple,
    Fin.sum_univ_succ, MME.StothersFourth.Phi116.cwO,
    MME.StothersFourth.Phi116.cwM, MME.StothersFourth.Phi116.cwT,
    hM, hT]
  abel_nf
