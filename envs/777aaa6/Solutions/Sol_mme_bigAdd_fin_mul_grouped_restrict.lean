-- Prove2me | solution 1 for mme_bigAdd_fin_mul_grouped_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:04:35.575852+00:00
-- url     : https://prove2.me/submissions/bd63e251-00a0-4222-bdd5-944e0b315948

import Theorems.Thm_mme_bigAdd_fin_mul_isomorphic_nested
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {d k g : ℕ}
    (X : Fin k → Fin g → TensorObj K d)
    (Y : Fin k → TensorObj K d)
    (hgroup : ∀ a, TensorObj.Restrict (Y a)
      (TensorObj.bigAdd (fun b : Fin g ↦ X a b))) :
    TensorObj.Restrict
      (TensorObj.bigAdd Y)
      (TensorObj.bigAdd (fun r : Fin (k * g) ↦
        X (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)) := by
  have hbig : TensorObj.Restrict
      (TensorObj.bigAdd Y)
      (TensorObj.bigAdd (fun a : Fin k ↦
        TensorObj.bigAdd (fun b : Fin g ↦ X a b))) :=
    mme_bigAdd_mono_restrict hgroup
  exact TensorObj.Restrict.trans hbig
    (mme_bigAdd_fin_mul_isomorphic_nested X).2
