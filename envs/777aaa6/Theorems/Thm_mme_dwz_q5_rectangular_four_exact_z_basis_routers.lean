-- Prove2me | Theorems.Thm_mme_dwz_q5_rectangular_four_exact_z_basis_routers
-- name    : mme_dwz_q5_rectangular_four_exact_z_basis_routers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:49:43.211548+00:00
-- url     : https://prove2.me/theorems/6a9f5f5d-e30d-4d3f-86db-25b6ae1ae984
-- title:
--   Four canonical q=5 rectangular CW-square routers with exact Z-basis coordinates
-- statement:
--   For every field $K$, the literal canonical $(0,1,3)$ and $(0,3,1)$ blocks of $\mathrm{CW}_5^{\otimes2}$ admit explicit restrictions to $\langle1,1,10\rangle_K$, and the $(1,0,3)$ and $(3,0,1)$ blocks admit explicit restrictions to $\langle10,1,1\rangle_K$. Each restriction sends every vector of the explicitly fixed canonical coarse-class $Z$ basis to a distinct standard target coordinate vector. Thus the restriction records exact $Z$-coordinate labels, not only an ordinary tensor restriction. These maps can be powered and followed by prescribed-coordinate projections. No asymptotic rate or global fourth-power extraction is asserted here.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Section 6.3, elementary boundary components. q=5 specialization of the accepted exact-Z rectangular router proof for q=6 (fc041b92-d7e8-4baa-9dc3-5894c14adab7 and its companion routers); the generic-q tensor identities are reused, while the finite canonical coordinate enumeration is checked at q=5. This four-router packaging is not separately numbered in the paper.

import Definitions.Def_mme_dwz_component_word_projection

open MME PiTensorProduct Module
open MME.DWZComponentRestriction
universe u
set_option autoImplicit false

theorem mme_dwz_q5_rectangular_four_exact_z_basis_routers (K : Type u) [Field K] :
    (∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 5).classOf s
            (cwSquareBlockType 0 1 3 s) →ₗ[K]
          (MMObj K 1 1 10).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 5).blockTensor
            (cwSquareBlockType 0 1 3)) =
        MMTensor K 1 1 10 ∧
      ∃ coord : LiftedCoarsePair.{u} 5 3 ↪ Fin 10,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 5 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 10 × Fin 1 → K)) ∧
    (∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 5).classOf s
            (cwSquareBlockType 0 3 1 s) →ₗ[K]
          (MMObj K 1 1 10).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 5).blockTensor
            (cwSquareBlockType 0 3 1)) =
        MMTensor K 1 1 10 ∧
      ∃ coord : LiftedCoarsePair.{u} 5 1 ↪ Fin 10,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 5 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 10 × Fin 1 → K)) ∧
    (∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 5).classOf s
            (cwSquareBlockType 1 0 3 s) →ₗ[K]
          (MMObj K 10 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 5).blockTensor
            (cwSquareBlockType 1 0 3)) =
        MMTensor K 10 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 5 3 ↪ Fin 10,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 5 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 10 → K)) ∧
    (∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 5).classOf s
            (cwSquareBlockType 3 0 1 s) →ₗ[K]
          (MMObj K 10 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 5).blockTensor
            (cwSquareBlockType 3 0 1)) =
        MMTensor K 10 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 5 1 ↪ Fin 10,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 5 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 10 → K)) := by sorry
