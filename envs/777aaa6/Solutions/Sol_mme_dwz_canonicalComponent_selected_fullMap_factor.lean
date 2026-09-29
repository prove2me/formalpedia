-- Prove2me | solution 1 for mme_dwz_canonicalComponent_selected_fullMap_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T09:36:26.618151+00:00
-- url     : https://prove2.me/submissions/cd8b771a-f2ee-476c-b810-1917f1c569aa

import Definitions.Def_mme_dwz_step1_source_address_projectors
import Definitions.Def_mme_dwz_basis_label_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_dwz_canonicalComponent_selected_fullMap_basis_zero

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K] (s : Fin 15)
    (selected : ∀ i : Fin 3,
      MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i))
    {W : Fin 3 → Type u}
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (post : ∀ i,
      (MME.DWZComponentRestriction.canonicalComponentBlock K s).V i →ₗ[K]
        W i)
    (i : Fin 3) :
    let componentMap := (post i).comp
      (MME.DWZComponentRestriction.basisLabelProjection
        (canonicalComponentModeBasis K s i) id {selected i})
    let fullMap := componentMap.comp
      ((cwSquareCanonicalGrading K 6).blockProj i
        (cwSquareBlockType
          (MME.DWZSquare.shapeX s)
          (MME.DWZSquare.shapeY s)
          (MME.DWZSquare.shapeZ s) i))
    fullMap.comp
        (MME.DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {(selected i).down.1}) =
      fullMap := by
  dsimp only
  apply (cwSquareCanonicalBasis K 6 i).ext
  intro p
  by_cases hp : p = (selected i).down.1
  · subst p
    simp only [LinearMap.comp_apply,
      MME.DWZComponentRestriction.basisLabelProjection,
      Module.Basis.constr_basis, id_eq, Finset.mem_singleton, if_true]
  · have hz :=
      mme_dwz_canonicalComponent_selected_fullMap_basis_zero
        (K := K) s selected post i p hp
    have hs :
        MME.DWZComponentRestriction.basisLabelProjection
          (cwSquareCanonicalBasis K 6 i) id {(selected i).down.1}
          (cwSquareCanonicalBasis K 6 i p) = 0 := by
      unfold MME.DWZComponentRestriction.basisLabelProjection
      rw [Module.Basis.constr_basis]
      simp only [id_eq, Finset.mem_singleton, if_neg hp]
    rw [LinearMap.comp_apply, hs]
    exact (LinearMap.map_zero _).trans hz.symm
