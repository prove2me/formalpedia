-- Prove2me | solution 1 for mme_kronFin_group_by_exact_fibers_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:36:32.898208+00:00
-- url     : https://prove2.me/submissions/e97b25ab-d899-408c-b402-e92801ea28cd

import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d N k : ℕ}
    (X : Fin k → TensorObj K d)
    (w : Fin N → Fin k) (multiplicity : Fin k → ℕ)
    (hcard : ∀ s : Fin k,
      Fintype.card {r : Fin N // w r = s} = multiplicity s) :
    TensorObj.Isomorphic
      (TensorObj.kronFin N (fun r ↦ X (w r)))
      (TensorObj.kronFin k (fun s ↦ (X s).kronPow (multiplicity s))) := by
  classical
  rw [← TensorQ.toQ_eq_iff]
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  simp_rw [TensorQ.toQ_kronPow]
  rw [← Finset.prod_fiberwise' Finset.univ w
    (fun s ↦ TensorQ.toQ (X s))]
  apply Finset.prod_congr rfl
  intro s _hs
  rw [Finset.prod_const]
  congr 1
  rw [← Fintype.card_subtype]
  exact hcard s
