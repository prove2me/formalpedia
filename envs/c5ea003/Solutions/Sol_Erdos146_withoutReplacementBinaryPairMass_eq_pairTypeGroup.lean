-- Prove2me | solution 1 for Erdos146.withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:19:49.941124+00:00
-- url     : https://prove2.me/submissions/bab8426d-93ed-44a6-8085-0f6aad505263

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Choose.Cast
import Theorems.Thm_Erdos146_pairTypeGroup_false_card
import Theorems.Thm_Erdos146_pairTypeGroup_true_card

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem sum_pairTypeGroup_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroup parents coordinate bitType).card) =
      parentCount.choose 2 := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hpairs :
      (Finset.univ : Finset (PairLayer parentCount 1)).card =
        parentCount.choose 2 := by
    rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  calc
    (∑ bitType : PairBitType,
        (pairTypeGroup parents coordinate bitType).card) =
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        simpa [pairTypeGroup] using hpartition.symm
    _ = parentCount.choose 2 := hpairs

theorem pairTypeGroup_mixed_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 2).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate) *
        pairParentCoordinateOneCount parents coordinate := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have htotal :
      (pairTypeGroup parents coordinate 0).card +
        (pairTypeGroup parents coordinate 1).card +
          (pairTypeGroup parents coordinate 2).card =
            parentCount.choose 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      sum_pairTypeGroup_card parents coordinate
  rw [pairTypeGroup_false_card,
    pairTypeGroup_true_card] at htotal
  have htotal_real :
      (((parentCount -
          pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        (((pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) =
          (parentCount.choose 2 : ℝ) := by
    exact_mod_cast htotal
  rw [Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_sub hones] at htotal_real
  have hresult :
      ((pairTypeGroup parents coordinate 2).card : ℝ) =
        (((parentCount -
          pairParentCoordinateOneCount parents coordinate) *
            pairParentCoordinateOneCount parents coordinate : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hones]
    nlinarith
  exact_mod_cast hresult

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have hparent : 0 < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  cases left <;> cases right <;>
    simp [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount,
      pairBitTypeOfOutcomes,
      pairTypeGroup_false_card,
      pairTypeGroup_true_card,
      pairTypeGroup_mixed_card,
      Nat.cast_choose_two,
      Nat.cast_sub hones] <;>
    field_simp [hparent.ne', hparent_minus.ne']
