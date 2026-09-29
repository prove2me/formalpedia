-- Prove2me | solution 1 for Erdos146.pairCoordinateConditionalEntropy_empirical_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:21:23.009887+00:00
-- url     : https://prove2.me/submissions/2486c48d-ca73-41b0-95d3-875787d2def5

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Field
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Theorems.Thm_Erdos146_empiricalConditionalEntropy_bound
import Theorems.Thm_Erdos146_pairCoordinateKernel_childProbability
import Theorems.Thm_Erdos146_pairTypeGroup_probability_mul_childRatio
import Theorems.Thm_Erdos146_withoutReplacementBinaryPairMass_eq_pairTypeGroup

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairCoordinateKernel_parentProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairCoordinateKernel hparents parents children coordinate).parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := by
  rfl

theorem sum_pairTypeGroupChildOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      pairChildCoordinateOneCount children coordinate := by
  classical
  let support : Finset (PairLayer parentCount 1) :=
    booleanWordOnes (fun pair => children pair coordinate)
  have hmaps :
      ((support : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1)).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : PairBitType) :
      support.filter
        (fun pair => pairCoordinateBitType parents coordinate pair = bitType) =
      pairTypeGroupChildOnes parents children coordinate bitType := by
    ext pair
    simp [support, booleanWordOnes,
      pairTypeGroupChildOnes, pairTypeGroup, and_comm]
  calc
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      ∑ bitType : PairBitType,
        (support.filter
          (fun pair =>
            pairCoordinateBitType parents coordinate pair = bitType)).card := by
          apply Finset.sum_congr rfl
          intro bitType _
          rw [hfiber]
    _ = support.card := by
      exact hpartition.symm
    _ = pairChildCoordinateOneCount children coordinate := by
      rfl

theorem pairCoordinateKernel_empiricalConditionalEntropy
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      pairCoordinateConditionalEntropy parents children coordinate := by
  unfold empiricalConditionalEntropy
    withoutReplacementBinaryPairExpectation
  simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
    hparents parents coordinate]
  simp [Fintype.univ_bool,
    pairCoordinateKernel_childProbability,
    pairBitTypeOfOutcomes,
    pairCoordinateConditionalEntropy,
    Fin.sum_univ_succ]
  ring

theorem pairCoordinateKernel_empiricalChildMarginal
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ) := by
  have hgroups :
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
    calc
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        ∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
              (parentCount.choose 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro bitType _
          exact pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType
      _ =
        (∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ)) /
            (parentCount.choose 2 : ℝ) := by
          rw [Finset.sum_div]
      _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          congr 1
          exact_mod_cast
            sum_pairTypeGroupChildOnes_card parents children coordinate
  calc
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
      unfold empiricalChildMarginal
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        Fin.sum_univ_succ]
      ring
    _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose 2 : ℝ) := hgroups

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  let kernel : BinaryPairKernel :=
    pairCoordinateKernel (by omega) parents children coordinate
  have hkernel := empiricalConditionalEntropy_bound
    parentCount (pairParentCoordinateOneCount parents coordinate)
      hparents hones kernel
      (pairCoordinateKernel_parentProbability
        (by omega) parents children coordinate)
  change
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate) ≤ _ at hkernel
  rw [pairCoordinateKernel_empiricalConditionalEntropy
    (by omega) parents children coordinate] at hkernel
  rw [pairCoordinateKernel_empiricalChildMarginal
    (by omega) parents children coordinate] at hkernel
  change
    pairCoordinateConditionalEntropy parents children coordinate ≤
      kappa +
        logTwo 3 *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount at hkernel
  exact hkernel
