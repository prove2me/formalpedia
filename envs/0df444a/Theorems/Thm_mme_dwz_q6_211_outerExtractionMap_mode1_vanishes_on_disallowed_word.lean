-- Prove2me | Theorems.Thm_mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
-- name    : mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:05:34.682143+00:00
-- url     : https://prove2.me/theorems/c5ca02e0-e11e-402a-9dfb-b98115ce0216
-- title:
--   The q=6 row-211 outer extraction kills every disallowed decoded word
-- statement:
--   For the q=6 Table-2 row 211, decode a canonical third-mode word through the exact row router into the coupled coordinate basis. If the original word fails the prescribed balanced Table-2 split, then the mode-one shared-Z primary-family outer extraction annihilates the decoded recursive product-basis vector. This is the exact zeroing clause required to descend the row-211 source map to its allowed-word projection.
-- source:
--   DWZ q=6 row-211 canonical source router and Coppersmith--Winograd primary-family outer extraction.

import Theorems.Thm_mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
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
        MME.DWZTable2Counts.split (14 : Fin 15) a * m) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 1
        (kronPowModeBasis (coupledObj K 6) 1
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
          (2 * (1036722900000000 * m))
          (PowIndex.ofFun (2 * (1036722900000000 * m))
            (fun r ↦ ULift.up (coord (PowIndex.get _ w r))))) =
      0 := by
  sorry
