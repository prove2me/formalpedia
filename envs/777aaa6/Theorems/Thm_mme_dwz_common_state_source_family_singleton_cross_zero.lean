-- Prove2me | Theorems.Thm_mme_dwz_common_state_source_family_singleton_cross_zero
-- name    : mme_dwz_common_state_source_family_singleton_cross_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:18:58.355342+00:00
-- url     : https://prove2.me/theorems/e35026bc-467a-4e50-a858-508f1281eac4
-- title:
--   Common-state surviving singleton kills a distinct Z owner
-- statement:
--   For owners in one canonical affine bucket and one shared affine state, a surviving Z-word singleton annihilates every mixed source-family term whose X/Y owner is common but whose Z owner is distinct.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Claim 6.2 and Claim 6.8; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps
import Definitions.Def_mme_dwz_global_common_state_broken_copy

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem mme_dwz_common_state_source_family_singleton_cross_zero
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hBucket : ∀ j, edge j ∈ dwzTable2AffineHashBucket S A q)
    (js : Fin 3 → Fin n)
    (h01 : js 0 = js 1) (h02 : js 0 ≠ js 2)
    (W : AddressZWord (sourceWord reindex edge (js 2)))
    (hSurvives : addressWordSurvives m
      (sourceWord reindex edge (js 2))
      (commonStateBrokenCopy m reindex q edge (js 2)) W) :
    let Source : TensorObj K 3 :=
      (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L
    let maps : ∀ i : Fin 3, Source.V i →ₗ[K]
        (brokenAddressObj K m
          (sourceWord reindex edge (js i))
          (commonStateBrokenCopy m reindex q edge (js i))).V i :=
      fun i ↦ step1FilteredBrokenSourceMaps K m
        (sourceWord reindex edge (js i))
        (commonStateBrokenCopy m reindex q edge (js i)) i
    let singleton :=
      DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K (sourceWord reindex edge (js 2))) id {W}
    let selectedZ :=
      (((step1FilteredBrokenAddressMaps K m
          (sourceWord reindex edge (js 2))
          (commonStateBrokenCopy m reindex q edge (js 2)) 2).comp
        singleton).comp
        (gradedAddressProj (cwSquareCanonicalGrading K 6) L
          (coarseAddress (sourceWord reindex edge (js 2))) 2))
    PiTensorProduct.map (Function.update maps 2 selectedZ) Source.t = 0 := by
  sorry
