-- Prove2me | solution 1 for mme_more_asymmetry_raw_recursive_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T17:21:54.846597+00:00
-- url     : https://prove2.me/submissions/188accd3-47f1-419f-988e-ac5bed5b3570

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_tensor_quotient

open MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

private theorem kron_mono {K : Type u} [Field K] {A A' B B' : TensorObj K 3}
    (ha : Restrict A A') (hb : Restrict B B') : Restrict (A.kron B) (A'.kron B') := by
  let P := TensorQ.tensorStrassen K 3 (by decide)
  have H1 : TensorQ.le (TensorQ.toQ A * TensorQ.toQ B) (TensorQ.toQ A' * TensorQ.toQ B) :=
    P.mul_right _ _ ha _
  have H2 : TensorQ.le (TensorQ.toQ A' * TensorQ.toQ B) (TensorQ.toQ A' * TensorQ.toQ B') := by
    simpa only [mul_comm] using P.mul_right (TensorQ.toQ B) (TensorQ.toQ B') hb (TensorQ.toQ A')
  exact H1.trans H2

private theorem kronFin_mono {K : Type u} [Field K] {k : ℕ}
    (A B : Fin k → TensorObj K 3) (h : ∀ j, Restrict (A j) (B j)) :
    Restrict (kronFin k A) (kronFin k B) := by
  induction k with
  | zero => exact Restrict.refl _
  | succ k ih => exact kron_mono (h 0) (ih _ _ (fun j ↦ h j.succ))

theorem solution {K : Type u} [Field K]
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (hcompat : MoreAsymmetryRawSourceCompatibility D A K) :
    TensorObj.Restrict
      (TensorObj.kronFin D.factors (fun j ↦ (A j).raw K))
      ((sixSymmetrization (StothersFourth.cwFourthObj K 5)).kronPow D.power) := by
  have hfactor := kronFin_mono
    (fun j ↦ (A j).raw K)
    (fun _ : Fin D.factors ↦ hcompat.source)
    hcompat.factor_restrict
  exact hfactor.trans hcompat.ambient_isomorphic.1
