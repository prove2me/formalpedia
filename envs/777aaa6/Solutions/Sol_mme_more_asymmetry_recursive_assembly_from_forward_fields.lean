-- Prove2me | solution 1 for mme_more_asymmetry_recursive_assembly_from_forward_fields
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T17:59:44.216548+00:00
-- url     : https://prove2.me/submissions/20de3cfd-3893-40b6-9343-0411ece5be0f

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_stage_certificate
import Theorems.Thm_mme_more_asymmetry_raw_recursive_assembly
import Theorems.Thm_mme_bigAdd_mono_restrict
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
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (localA localB localC : Fin D.factors → ℕ)
    (hfactor_template :
      ∀ j, TensorObj.Restrict
        (MMObj K (localA j) (localB j) (localC j))
        ((A j).template K))
    (hprod_a : (∏ j, localA j) = D.a)
    (hprod_b : (∏ j, localB j) = D.b)
    (hprod_c : (∏ j, localC j) = D.c)
    (hcopy :
      ∀ counts : Fin D.factors → ℕ,
        (∀ j, (D.hash j).lower ≤ (counts j : ℝ)) →
        TensorObj.Restrict
          (TensorObj.bigAdd
            (fun _ : Fin ((∏ j, counts j) / D.repairCopies) ↦
              MMObj K D.a D.b D.c))
          (TensorObj.kronFin D.factors
            (fun j ↦ TensorObj.bigAdd
              (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦
                MMObj K (localA j) (localB j) (localC j))))) :
    RecursiveAssembly D A K := by
  refine ⟨mme_more_asymmetry_raw_recursive_assembly D A hraw, ?_⟩
  intro counts hcounts
  have hfactor :
      ∀ j, TensorObj.Restrict
        (TensorObj.bigAdd
              (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦
                MMObj K (localA j) (localB j) (localC j)))
        (TensorObj.bigAdd
          (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦ (A j).template K)) := by
    intro j
    exact mme_bigAdd_mono_restrict (fun _ ↦ hfactor_template j)
  have hkron := kronFin_mono
    (fun j ↦ TensorObj.bigAdd
      (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦
        MMObj K (localA j) (localB j) (localC j)))
    (fun j ↦ TensorObj.bigAdd
      (fun _ : Fin (counts j / 8 ^ (A j).repairExponent) ↦ (A j).template K))
    hfactor
  exact (hcopy counts hcounts).trans hkron
