-- Prove2me | solution 1 for mme_complete_split_cw_fourth_label_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:45:05.58718+00:00
-- url     : https://prove2.me/submissions/718a05de-6ae8-4497-9d9e-91746cf838b1

import Definitions.Def_mme_complete_split_cw_fourth_labels
import Mathlib.Tactic

set_option autoImplicit false

universe u

open MME Module BigOperators MME.StothersFourth MME.DWZComponentRestriction
open MME.CompleteSplit MME.CompleteSplit.CWFourth
open scoped NNReal
set_option warningAsError true

namespace MME.CompleteSplit.CWFourth

private theorem fullWord_sum (q : ℕ) (p : Coordinate q) :
    (∑ r : Fin 4, (fullWord q p r).val) = (cwFourthPairGrade q p).val := by
  simp [fullWord, Fin.sum_univ_succ, cwFourthPairGrade, cwSquarePairGrade]
  omega

private theorem coarseClassBasis_coe
    (K : Type u) [Field K] (q : ℕ) (i : Fin 3) (c : Fin 9)
    (p : CoarseCoordinate q c) :
    (coarseClassBasis K q i c p).val = cwFourthCanonicalBasis K q i p.1 := by
  simp only [coarseClassBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Basis.span_apply]
  rfl

private theorem constituentBasis_coe
    (K : Type u) [Field K] (q : ℕ) (I J L : Fin 9) (i : Fin 3)
    (p : LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) :
    (constituentBasis K q I J L i p).val =
      cwFourthCanonicalBasis K q i p.down.1 := by
  have h := congrArg Subtype.val
    ((coarseClassBasis K q i (cwFourthBlockType I J L i)).reindex_apply
      Equiv.ulift.symm p)
  exact h.trans (coarseClassBasis_coe K q i _ p.down)

private theorem constituentLabel_sum
    (q : ℕ) (I J L : Fin 9) (i : Fin 3)
    (p : LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) :
    (∑ r : Fin 4, (constituentLabel q I J L i p r).val) =
      (cwFourthBlockType I J L i).val := by
  exact (fullWord_sum q p.down.1).trans (congrArg Fin.val p.down.2)

private theorem constituent_wordCount_eq_zero_of_wrong_grade
    (q : ℕ) (I J L : Fin 9) (i : Fin 3) (N : ℕ)
    (w : PowIndex (LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) N)
    (sigma : CompleteWord 3)
    (hgrade : (∑ r : Fin 4, (sigma r).val) ≠ (cwFourthBlockType I J L i).val) :
    wordCount (constituentLabel q I J L i) w sigma = 0 := by
  unfold wordCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro r _ heq
  apply hgrade
  have h := constituentLabel_sum q I J L i (PowIndex.get N w r)
  rwa [heq] at h

end MME.CompleteSplit.CWFourth

theorem solution
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
        wordCount (constituentLabel q I J L i) w sigma = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun i p ↦ constituentBasis_coe K q I J L i p
  · exact fun i p ↦ constituentLabel_sum q I J L i p
  · exact fun i N w sigma hgrade ↦
      constituent_wordCount_eq_zero_of_wrong_grade q I J L i N w sigma hgrade

