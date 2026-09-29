-- Prove2me | Theorems.Thm_mme_more_asymmetry_raw_recursive_assembly
-- name    : mme_more_asymmetry_raw_recursive_assembly
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T17:20:35.053815+00:00
-- url     : https://prove2.me/theorems/c98241d1-fb72-47b6-a07b-0cf2a058715d
-- title:
--   More Asymmetry raw assembly from source compatibility
-- statement:
--   Let $D$ be a finite More Asymmetry data bundle and let $A$ attach one concrete recursive stage to each hash factor. Assume the independently meaningful raw-source compatibility interface: every literal stage source restricts to one common factor source, and the finite Kronecker product of those factor sources is isomorphic to the declared six-symmetrised fourth-power $CW_5$ source. Then the Kronecker product of the literal stage sources restricts to the campaign source. This is only the raw-source half of the recursive assembly; it makes no assertion about intact templates, matrix dimensions, copy counts, budgets, or the rate certificate.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.1 and 6.1--6.6. This finite raw-source assembly isolates the source restriction and six-region power compatibility before the intact-template/MM assembly.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility

open MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

theorem mme_more_asymmetry_raw_recursive_assembly {K : Type u} [Field K]
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (hcompat : MoreAsymmetryRawSourceCompatibility D A K) :
    TensorObj.Restrict
      (TensorObj.kronFin D.factors (fun j ↦ (A j).raw K))
      ((sixSymmetrization (StothersFourth.cwFourthObj K 5)).kronPow D.power) := by sorry
