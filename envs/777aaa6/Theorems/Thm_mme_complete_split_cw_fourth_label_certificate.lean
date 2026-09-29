-- Prove2me | Theorems.Thm_mme_complete_split_cw_fourth_label_certificate
-- name    : mme_complete_split_cw_fourth_label_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T21:27:27.197648+00:00
-- url     : https://prove2.me/theorems/4efc771f-843b-4484-ae11-c21507c9f634
-- title:
--   Canonical CW fourth labels identify the literal basis and coarse support
-- statement:
--   For any field and q, each mode-basis vector of the actual coarse fourth constituent is exactly its indicated canonical fourth basis vector after inclusion. Its complete four-letter word has total grade I, J, or L in the corresponding mode. Consequently a full word with another total grade occurs zero times in every power-basis word. This is a literal finite support certificate; it does not establish that a chosen approximate profile is feasible or that a retained tensor is nonzero.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, printed pp.14-15, Definitions 3.4-3.6. Literal level-three full-word labels on the existing fourth-power CW tensor; q=5 is the More Asymmetry consumer.

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic

set_option autoImplicit false

universe u

open MME Module BigOperators MME.StothersFourth MME.DWZComponentRestriction
open MME.CompleteSplit MME.CompleteSplit.CWFourth
open scoped NNReal

theorem mme_complete_split_cw_fourth_label_certificate
    {K : Type u} [Field K] (q : ℕ) (I J L : Fin 9) :
    (∀ (i : Fin 3)
      (p : LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)),
      (constituentBasis K q I J L i p).val =
        cwFourthCanonicalBasis K q i p.down.1) ∧
    (∀ (i : Fin 3)
      (p : LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)),
      (∑ r : Fin 4, (constituentLabel q I J L i p r).val) =
        (cwFourthBlockType I J L i).val) ∧
    (∀ (i : Fin 3) (N : ℕ)
      (w : PowIndex (LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) N)
      (sigma : CompleteWord 3),
      (∑ r : Fin 4, (sigma r).val) ≠ (cwFourthBlockType I J L i).val →
        wordCount (constituentLabel q I J L i) w sigma = 0) := by sorry
