-- Prove2me | solution 1 for mme_more_asymmetry_template_mm_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T17:25:40.257648+00:00
-- url     : https://prove2.me/submissions/9dbac0d8-ff9a-40df-8a28-fbf784d45a75

import Definitions.Def_mme_more_asymmetry_template_mm_compatibility
import Theorems.Thm_mme_kronFin_MMObj_iso
import Definitions.Def_mme_tensor_quotient

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate

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
    (hcompat : MoreAsymmetryTemplateMMCompatibility D A K) :
    TensorObj.Restrict
      (TensorObj.kronFin D.factors (fun j ↦ (A j).template K))
      (MMObj K D.a D.b D.c) := by
  have hfactor := kronFin_mono
    (fun j ↦ (A j).template K)
    (fun j ↦ MMObj K (hcompat.localA j) (hcompat.localB j) (hcompat.localC j))
    hcompat.factor_restrict
  have hiso := mme_kronFin_MMObj_iso (K := K) D.factors
    hcompat.localA hcompat.localB hcompat.localC
  have htarget :
      Restrict
        (TensorObj.kronFin D.factors
          (fun j ↦ MMObj K (hcompat.localA j) (hcompat.localB j) (hcompat.localC j)))
        (MMObj K D.a D.b D.c) := by
    simpa [hcompat.product_a, hcompat.product_b, hcompat.product_c] using hiso.1
  exact hfactor.trans htarget
