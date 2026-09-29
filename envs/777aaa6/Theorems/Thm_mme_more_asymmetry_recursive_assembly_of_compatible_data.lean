-- Prove2me | Theorems.Thm_mme_more_asymmetry_recursive_assembly_of_compatible_data
-- name    : mme_more_asymmetry_recursive_assembly_of_compatible_data
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-12T17:31:32.349274+00:00
-- url     : https://prove2.me/theorems/680baca7-fd08-4ba2-a091-0bd7e30821e4
-- title:
--   More Asymmetry RecursiveAssembly from source-compatible data
-- statement:
--   If one concrete More Asymmetry data/stage family supplies three explicit source-level hypotheses on the same D and A—raw-source compatibility, factorwise intact-template/MM restrictions with product dimensions, and the finite repaired-copy restriction after replacing templates by local MM tensors—then the live RecursiveAssembly predicate follows. No hypothesis is itself RecursiveAssembly; the proof composes the published raw assembly theorem with factorwise finite-direct-sum monotonicity and the supplied copy arrangement.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.1 and 6.1--6.6. The theorem is the source-faithful composition of raw source compatibility, intact-template profile restrictions, and finite repaired-copy accounting.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_more_asymmetry_template_mm_compatibility
import Definitions.Def_mme_recursive_yz_stage_certificate
import Theorems.Thm_mme_more_asymmetry_raw_recursive_assembly
import Definitions.Def_mme_tensor_quotient

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

theorem mme_more_asymmetry_recursive_assembly_of_compatible_data {K : Type u} [Field K]
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (htemplate : MoreAsymmetryTemplateMMCompatibility D A K)
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
                MMObj K (htemplate.localA j) (htemplate.localB j)
                  (htemplate.localC j))))) :
    RecursiveAssembly D A K := by sorry
