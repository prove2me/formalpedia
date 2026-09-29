-- Prove2me | Theorems.Thm_mme_dwz_q6_112_router_projector_descent
-- name    : mme_dwz_q6_112_router_projector_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:48:21.253836+00:00
-- url     : https://prove2.me/theorems/2f33322b-91d0-4aec-9961-28338b2c598d
-- title:
--   Exact-address projector extraction descends through the enhanced 112 profile
-- statement:
--   Fix the enhanced q=6 canonical 112 block at Table-2 scale m. Suppose a basis-labelled one-letter router is powered to the full row-12 word length, and suppose the subsequent extraction is a finite sum of projectors indexed by exact enhanced-112 addresses, followed by arbitrary linear postmaps. If the router translates canonical left grades by 0,1,2 ↦ 2,0,1 and both powered stages preserve their stated tensors, then the resulting restriction factors through the literal allowed-word tensor `restrictedComponentPower K 12 m`. The theorem packages the exact chain profile mismatch → projector zero → finite-sum zero → basis-Z descent, leaving only the concrete router and `outerExtractionMap` decomposition to instantiate.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.4 and the hashing/restriction construction in Sections 5–6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_q6_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Theorems.Thm_mme_kronPowModeMap_recursive_basis
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module
open BigOperators

universe u

set_option autoImplicit false

theorem mme_dwz_q6_112_router_projector_descent
    {K : Type u} [Field K] (m : ℕ)
    (C A : TensorObj K 3) (G : C.TypeGrading 3)
    {I J : Type u} [Fintype J]
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
