-- Prove2me | Theorems.Thm_mme_dwz_canonical_component_row_cast_exact
-- name    : mme_dwz_canonical_component_row_cast_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:46:06.953556+00:00
-- url     : https://prove2.me/theorems/bcf50ff5-4053-4b96-8287-64182b3ce338
-- title:
--   Canonical Table-2 row casts preserve the literal tensor and Z basis
-- statement:
--   If two Table-2 row labels are equal, the canonical modewise transports between their component tensors preserve the literal tensor. On the $Z$ mode, every canonical basis vector is sent exactly to the basis vector indexed by the transported letter, and the transported letter is heterogeneously equal to the original one. Thus row regrouping changes neither tensor coefficients nor canonical coordinates.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 (Table-2 component words and regrouping), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_canonical_component_row_cast_data
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_dwz_canonical_component_row_cast_exact
    {K : Type u} [Field K] {s t : Fin 15} (h : s = t) :
    PiTensorProduct.map
        (fun i ↦ (MME.DWZSourceAligned.canonicalComponentModeCast
          (K := K) h i).toLinearMap)
        (MME.DWZComponentRestriction.canonicalComponentBlock K s).t =
      (MME.DWZComponentRestriction.canonicalComponentBlock K t).t ∧
    (∀ x : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s),
      HEq
        (MME.DWZSourceAligned.canonicalComponentModeCast (K := K) h 2
          (MME.DWZComponentRestriction.canonicalComponentZBasis K s x))
        (MME.DWZComponentRestriction.canonicalComponentZBasis K t
          (MME.DWZSourceAligned.canonicalComponentZLetterCast h x))) ∧
    ∀ x : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
        (MME.DWZSquare.shapeZ s),
      HEq (MME.DWZSourceAligned.canonicalComponentZLetterCast h x) x := by
  sorry
