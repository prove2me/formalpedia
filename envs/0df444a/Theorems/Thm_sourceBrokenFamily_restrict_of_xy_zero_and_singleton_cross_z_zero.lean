-- Prove2me | Theorems.Thm_sourceBrokenFamily_restrict_of_xy_zero_and_singleton_cross_z_zero
-- name    : sourceBrokenFamily_restrict_of_xy_zero_and_singleton_cross_z_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T19:30:31.25205+00:00
-- url     : https://prove2.me/theorems/3c99a822-8cb7-4826-9cd5-5480d859e620
-- title:
--   Singleton mixed-Z annihilation assembles source-aligned broken owners
-- statement:
--   Consider a finite family of source-aligned broken copies inside a power of the squared Coppersmith–Winograd tensor. Assume every mixed choice with different X and Y owners is annihilated. For a mixed choice with a common X/Y owner and a distinct Z owner, assume only that each surviving singleton canonical Z-basis word of the Z owner is annihilated. Then the direct sum of all whole broken-address objects is a restriction of the full tensor power.

import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons
import Theorems.Thm_mme_dwz_source_broken_owner_projector_diagonal
import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Definitions.Def_mme_dwz_source_aligned_broken_obj
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem sourceBrokenFamily_restrict_of_xy_zero_and_singleton_cross_z_zero
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hXYZero : ∀ js : Fin 3 → Fin k,
      js 0 ≠ js 1 →
      PiTensorProduct.map
          (fun i ↦
            ((brokenAddressGrading K m (outer (js i))
                (copy (js i))).blockProj i 0).comp
              (gradedAddressProj (cwSquareCanonicalGrading K 6) N
                (coarseAddress (outer (js i))) i))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = 0)
    (hSingletonCross : ∀ (js : Fin 3 → Fin k),
      js 0 = js 1 → js 0 ≠ js 2 →
      ∀ W : AddressZWord (outer (js 2)),
      addressWordSurvives m (outer (js 2)) (copy (js 2)) W →
      let S : TensorObj K 3 :=
        (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N
      let maps : ∀ i : Fin 3, S.V i →ₗ[K]
          (brokenAddressObj K m (outer (js i)) (copy (js i))).V i :=
        fun i ↦
          ((brokenAddressGrading K m (outer (js i))
              (copy (js i))).blockProj i 0).comp
            (gradedAddressProj (cwSquareCanonicalGrading K 6) N
              (coarseAddress (outer (js i))) i)
      let singleton :=
        MME.DWZComponentRestriction.basisLabelProjection
          (coarseAddressZBasis K (outer (js 2))) id {W}
      PiTensorProduct.map
          (Function.update maps 2
            ((((brokenAddressGrading K m (outer (js 2))
                  (copy (js 2))).blockProj 2 0).comp singleton).comp
              (gradedAddressProj (cwSquareCanonicalGrading K 6) N
                (coarseAddress (outer (js 2))) 2))) S.t = 0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        brokenAddressObj K m (outer j) (copy j)))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N) := by
  sorry
