-- Prove2me | Theorems.Thm_mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj
-- name    : mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T19:20:28.545728+00:00
-- url     : https://prove2.me/theorems/f21b752d-c1f9-49a6-92a1-6111b0ca2912
-- title:
--   Canonical q=6 row-112 Z basis is the grade-two block projection
-- statement:
--   For q=6, every labelled Z-basis vector of the literal Table-2 row-112 component is exactly the grade-(2,2) projection of its corresponding ambient canonical square-basis vector. This identifies the concrete restricted-component basis with the basis-labelled grading projector used by the enhanced 112 exact-address router.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and the enhanced 112 component analysis in Sections 4 and 6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val
import Definitions.Def_mme_TypeGrading_kron

open MME Module MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonicalComponent112_Z_basis_eq_blockProj
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 2) :
    canonicalComponentZBasis K 12 p =
      (cwSquareCanonicalGrading K 6).blockProj 2 2
        (cwSquareCanonicalBasis K 6 2 p.down.1) := by
  sorry
