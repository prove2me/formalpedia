-- Prove2me | Theorems.Thm_mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
-- name    : mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:59:57.19898+00:00
-- url     : https://prove2.me/theorems/27f7a2ee-b123-41e1-b9a4-5770abcce2b6
-- title:
--   Row-121 mode-zero outer extraction kills disallowed words
-- statement:
--   Set $N=1036722900000000m$, and let $w$ be a length-$2N$ canonical word in the row-121 component. Suppose the left-grade histogram of $w$ differs from the prescribed row-121 profile $(N,N,0)$. After applying the exact coordinate decoder from canonical row-121 indices to the ordinary coupled mode-zero basis, the shared-$Z$ outer-extraction map associated with any primary hash family annihilates the resulting basis word.
--
--   Equivalently, every retained outer-extraction slot has zero projection on a decoded word excluded by the row-121 availability condition. This is the mode-zero projector-absorption step needed to descend the cyclically normalized row-121 router to the literal restricted component.
-- source:
--   Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3 and Table 2, row 121; formal projector consequence of Definition 5.4 availability and the exact q=6 primary-family marginal profile.

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_dwz_component_disallowed_word_mismatches_profile
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H)
    (coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6))
    (hcoord : ∀ p,
      p.leftGrade =
        Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
          (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p))
    (w : PowIndex (LiftedCoarsePair.{u} 6 1)
      (2 * (1036722900000000 * m)))
    (hnot : ¬ ∀ a : Fin 3,
      Fintype.card
          {r : Fin (2 * (1036722900000000 * m)) //
            (PowIndex.get _ w r).leftGrade = a} =
        MME.DWZTable2Counts.split (13 : Fin 15) a * m) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 0
        (kronPowModeBasis (coupledObj K 6) 0
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
          (2 * (1036722900000000 * m))
          (PowIndex.ofFun (2 * (1036722900000000 * m))
            (fun r ↦ ULift.up (coord (PowIndex.get _ w r))))) =
      0 := by
  sorry
