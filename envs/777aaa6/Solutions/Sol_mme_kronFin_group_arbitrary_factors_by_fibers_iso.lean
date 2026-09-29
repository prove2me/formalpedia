-- Prove2me | solution 1 for mme_kronFin_group_arbitrary_factors_by_fibers_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:51:29.266541+00:00
-- url     : https://prove2.me/submissions/bac9dc04-efd6-42db-bb13-ccfacd471bac

import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d N k : ℕ}
    (X : Fin N → TensorObj K d) (label : Fin N → Fin k)
    (multiplicity : Fin k → ℕ)
    (fiberEquiv : ∀ s : Fin k,
      Fin (multiplicity s) ≃ {r : Fin N // label r = s}) :
    TensorObj.Isomorphic
      (TensorObj.kronFin N X)
      (TensorObj.kronFin k (fun s ↦
        TensorObj.kronFin (multiplicity s) (fun j ↦
          X ((fiberEquiv s j).1)))) := by
  classical
  rw [← TensorQ.toQ_eq_iff]
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  simp_rw [mme_toQ_kronFin]
  let e : (Σ s : Fin k, Fin (multiplicity s)) ≃ Fin N :=
    (Equiv.sigmaCongrRight fiberEquiv).trans
      (Equiv.sigmaFiberEquiv label)
  calc
    (∏ r : Fin N, TensorQ.toQ (X r)) =
        ∏ z : Σ s : Fin k, Fin (multiplicity s),
          TensorQ.toQ (X (e z)) := by
      symm
      exact Fintype.prod_equiv e
        (fun z : Σ s : Fin k, Fin (multiplicity s) ↦
          TensorQ.toQ (X (e z)))
        (fun r : Fin N ↦ TensorQ.toQ (X r))
        (fun _ ↦ rfl)
    _ = ∏ s : Fin k, ∏ j : Fin (multiplicity s),
          TensorQ.toQ (X ((fiberEquiv s j).1)) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro s _hs
      apply Finset.prod_congr rfl
      intro j _hj
      rfl
