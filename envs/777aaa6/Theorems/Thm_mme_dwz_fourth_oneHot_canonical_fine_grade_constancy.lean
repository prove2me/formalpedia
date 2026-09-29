-- Prove2me | Theorems.Thm_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy
-- name    : mme_dwz_fourth_oneHot_canonical_fine_grade_constancy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T05:38:22.308778+00:00
-- url     : https://prove2.me/theorems/abd1ba2e-07f5-48bc-b6cd-a80a850d18b9
-- title:
--   Constancy of the canonical fine grade on one-hot ledger rows
-- statement:
--   This file isolates the finite coordinate calculation behind the canonical grading. At q = 5, a CW coordinate has grade 0, 1, or 2; square and fourth coordinates have the sum grades used verbatim by cwSquareCanonicalGrading and StothersFourth.cwFourthCanonicalGrading. The restricted-basis index of a block is the fiber of the corresponding sum grade. The ledger calculation below proves that, on every one-hot row, the Z-block total is extreme: 0 or 4 at square level and 0 or 8 at fourth level. Hence every coordinate in its canonical fiber has the same first factor grade, exactly the active cell of the ledger profile. The six atomic rows use the integration's documented sentinel normalization: their whole canonical block fiber is assigned the single grade 0 : Fin 2.
--
--   The statement is the conjunction of 5 facts about this stage of the fourth-power assembly:
--
--   (1) A square total-zero fiber has first coordinate grade zero.
--
--   (2) A square total-four fiber has first coordinate grade two.
--
--   (3) A fourth total-zero fiber has first square grade zero.
--
--   (4) A fourth total-eight fiber has first square grade four.
--
--   (5) The active cell recorded by every one-hot row passes the exact canonical extreme-fiber criterion.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_oneHot_canonical_fine_grade_constancy_data
import Theorems.Thm_mme_dwz_fourth_oneHot_40_prescribedZ_endpoints

open MME MME.DWZFourthTensorLedger MME.DWZFourthTensorLedger.OneHotCanonicalFineGrade
open MME.DWZFourthTensorLedger
open MME.DWZFourthTensorLedger.OneHotEndpoints
open Module
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_oneHot_canonical_fine_grade_constancy :
    (∀ (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 0),
      q5CoordGrade ab.1 = 0) ∧
    (∀ (ab : Fin 7 × Fin 7) (h : q5SquarePairGrade ab = 4),
      q5CoordGrade ab.1 = 2) ∧
    (∀ (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) (h : q5FourthPairGrade p = 0),
      q5SquarePairGrade p.1 = 0) ∧
    (∀ (p : (Fin 7 × Fin 7) × (Fin 7 × Fin 7)) (h : q5FourthPairGrade p = 8),
      q5SquarePairGrade p.1 = 4) ∧
    (∀ (i : Fin 180) (hi : hasOneHotLedgerZProfile (componentSpecAt i) = true),
      canonicalExtremeActiveMatches (componentSpecAt i).address
        (activeGrade i) = true) := by sorry
