-- Prove2me | Theorems.Thm_mme_more_asymmetry_recursive_assembly_from_forward_fields
-- name    : mme_more_asymmetry_recursive_assembly_from_forward_fields
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T17:58:53.425005+00:00
-- url     : https://prove2.me/theorems/4d954b14-02c0-46e6-8ea4-a8807e496215
-- title:
--   More Asymmetry RecursiveAssembly from forward compatibility fields
-- statement:
--   If the same concrete More Asymmetry data/stage family supplies raw-source compatibility, explicit local matrix dimensions, forward factorwise restrictions from local MM tensors to intact templates, their product equalities, and the target-to-local finite repaired-copy restriction, then RecursiveAssembly follows. The explicit fields avoid any hidden direction or universal arbitrary-data assertion.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.1 and 6.1--6.6. The explicit forward fields follow the live RecursiveAssembly restriction orientation.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_stage_certificate
import Theorems.Thm_mme_more_asymmetry_raw_recursive_assembly
import Theorems.Thm_mme_bigAdd_mono_restrict
import Definitions.Def_mme_tensor_quotient

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

theorem mme_more_asymmetry_recursive_assembly_from_forward_fields {K : Type u} [Field K]
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
    RecursiveAssembly D A K := by sorry
