-- Prove2me | Theorems.Thm_mme_dwz_q6_112_router_projector_descent_poly
-- name    : mme_dwz_q6_112_router_projector_descent_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T21:35:09.276214+00:00
-- url     : https://prove2.me/theorems/73f5a14d-e5d9-49ff-b3e3-c61eb7b6680f
-- title:
--   Enhanced-112 projector descent with an independent finite index universe
-- statement:
--   Fix the enhanced q=6 row-112 component at Table-2 scale. A basis-labelled powered source router followed by a finite sum of exact-address projectors descends through the literal prescribed-profile subtensor whenever every disallowed word mismatches every exact address. The projector family may be indexed in a universe independent of the coefficient field, which is needed for concrete finite families such as Fin A.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4 and Sections 5-6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_q6_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Theorems.Thm_mme_kronPowModeMap_recursive_basis
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module
open BigOperators

universe u w

set_option autoImplicit false

theorem mme_dwz_q6_112_router_projector_descent_poly
    {K : Type u} [Field K] (m : ℕ)
    (C A : TensorObj K 3) (G : C.TypeGrading 3)
    {I : Type u} {J : Type w} [Fintype J]
    (cZ : Basis I K (C.V 2)) (targetGrade : I → Fin 3)
    (router : ∀ i : Fin 3,
      (canonicalComponentBlock K 12).V i →ₗ[K] C.V i)
    (label : LiftedCoarsePair.{u} 6 2 → I)
    (hrouterZ : ∀ p,
      router 2 (canonicalComponentZBasis K 12 p) = cZ (label p))
    (htranslate : ∀ p,
      p.leftGrade =
        mme_dwz_q6_coupled_Z_leftGrade (targetGrade (label p)))
    (exactAddress : J → CWQ6ExactCoupledAddress
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)))
    (address : J → Fin 3 →
      Fin (MME.DWZTable2Counts.component (12 : Fin 15) * m) → Fin 3)
    (haddress : ∀ (j : J)
      (hlen : MME.DWZTable2Counts.component (12 : Fin 15) * m =
        2 * (50000000 * (20088623 * m))) (i) (r),
      address j i r = (exactAddress j).1 i (Fin.cast hlen r))
    (post : ∀ j : J,
      (gradedAddressBlock G (address j)).V 2 →ₗ[K] A.V 2)
    (extract : ∀ i : Fin 3,
      (C.kronPow
        (MME.DWZTable2Counts.component (12 : Fin 15) * m)).V i →ₗ[K]
        A.V i)
    (hGzero : ∀ (a : Fin 3) (j : I), targetGrade j ≠ a →
      G.blockProj 2 a (cZ j) = 0)
    (hextractZ : extract 2 =
      ∑ j : J, (post j).comp
        (gradedAddressProj G
          (MME.DWZTable2Counts.component (12 : Fin 15) * m)
          (address j) 2))
    (hrouterPow :
      PiTensorProduct.map
          (fun i ↦ kronPowModeMap i (router i)
            (MME.DWZTable2Counts.component (12 : Fin 15) * m))
          ((canonicalComponentBlock K 12).kronPow
            (MME.DWZTable2Counts.component (12 : Fin 15) * m)).t =
        (C.kronPow
          (MME.DWZTable2Counts.component (12 : Fin 15) * m)).t)
    (hextractTensor :
      PiTensorProduct.map extract
          (C.kronPow
            (MME.DWZTable2Counts.component (12 : Fin 15) * m)).t =
        A.t) :
    TensorObj.Restrict A (restrictedComponentPower K 12 m) := by
  sorry
