-- Prove2me | solution 1 for mme_sixSymmetrization_kronFin_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:35:21.350563+00:00
-- url     : https://prove2.me/submissions/4702ee5e-ba5d-4ed2-af93-0fb663bcab4c

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u


set_option autoImplicit false
set_option warningAsError true

namespace SixSymKronFinSolution

theorem cyclicSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦ cyclicSymmetrization (T i)))
      (cyclicSymmetrization (TensorObj.kronFin n T)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin]
  rw [cyclicSymmetrization_eq_public_perm]
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  rw [← TensorQ.permAut_toQ, ← TensorQ.permAut_toQ]
  simp_rw [mme_toQ_kronFin]
  rw [map_prod, map_prod]
  simp_rw [cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.permAut_toQ]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

end SixSymKronFinSolution

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦ sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  apply (TensorQ.toQ_eq_iff).1
  rw [mme_toQ_kronFin]
  change
    ∏ i, TensorQ.toQ (sixSymmetrization (T i)) =
      TensorQ.toQ
        (TensorObj.kron
          (cyclicSymmetrization (TensorObj.kronFin n T))
          (TensorObj.permObj swapFirstTwoPerm
            (cyclicSymmetrization (TensorObj.kronFin n T))))
  rw [TensorQ.toQ_kron]
  have hcyclicQ := (TensorQ.toQ_eq_iff).2
    (SixSymKronFinSolution.cyclicSymmetrization_kronFin_isomorphic T)
  rw [← hcyclicQ]
  rw [← TensorQ.permAut_toQ]
  rw [← hcyclicQ]
  simp_rw [mme_toQ_kronFin]
  change
    ∏ i, TensorQ.toQ (sixSymmetrization (T i)) =
      (∏ i, TensorQ.toQ (cyclicSymmetrization (T i))) *
        TensorQ.permAut swapFirstTwoPerm
          (∏ i, TensorQ.toQ (cyclicSymmetrization (T i)))
  rw [map_prod, ← Finset.prod_mul_distrib]
  simp_rw [show ∀ i, sixSymmetrization (T i) =
      TensorObj.kron (cyclicSymmetrization (T i))
        (TensorObj.permObj swapFirstTwoPerm
          (cyclicSymmetrization (T i))) from fun _ ↦ rfl,
    TensorQ.toQ_kron, TensorQ.permAut_toQ]
