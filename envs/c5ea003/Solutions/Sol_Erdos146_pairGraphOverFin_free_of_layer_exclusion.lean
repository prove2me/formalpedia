-- Prove2me | solution 1 for Erdos146.pairGraphOverFin_free_of_layer_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:43:18.878081+00:00
-- url     : https://prove2.me/submissions/13c81662-b0af-4c4a-a284-6afe4ffaf071

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Field
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.InformationTheory.Hamming
import Theorems.Thm_Erdos146_hammingHost_adj_iff
import Theorems.Thm_Erdos146_pairCoordinateKernel_childProbability
import Theorems.Thm_Erdos146_pairCoordinatePairMismatchCount_homogeneous
import Theorems.Thm_Erdos146_pairGraphOverFin_free_of_layer_exclusion_and_disagreement
import Theorems.Thm_Erdos146_pairGraph_parent_child_adj
import Theorems.Thm_Erdos146_pairTypeGroup_probability_mul_childRatio
import Theorems.Thm_Erdos146_withoutReplacementBinaryPairMass_eq_pairTypeGroup

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairTypeGroup_probability_mul_childComplement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
  calc
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        (((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) := by
          ring
    _ = ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          rw [pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType]
    _ = (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
          ring

theorem pairCoordinateKernel_empiricalAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
  have hzero := pairTypeGroup_probability_mul_childRatio
    hparents parents children coordinate 0
  have hone := pairTypeGroup_probability_mul_childComplement
    hparents parents children coordinate 1
  calc
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((pairTypeGroup parents coordinate 0).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (((pairTypeGroupChildOnes parents children
          coordinate 0).card : ℝ) /
            ((pairTypeGroup parents coordinate 0).card : ℝ)) +
      ((pairTypeGroup parents coordinate 2).card : ℝ) /
          (parentCount.choose 2 : ℝ) * (1 / 2 : ℝ) +
      ((pairTypeGroup parents coordinate 1).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (1 -
          ((pairTypeGroupChildOnes parents children
            coordinate 1).card : ℝ) /
              ((pairTypeGroup parents coordinate 1).card : ℝ)) := by
      unfold empiricalAverageDisagreement
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        BinaryPairKernel.bitDisagreementProbability]
      ring
    _ =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
      rw [hzero, hone]
      ring

theorem pairCoordinatePairMismatchCount_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (hgroup : pairCoordinateBitType parents coordinate pair = 2) :
    pairCoordinatePairMismatchCount parents children coordinate pair = 1 := by
  classical
  have hnotfalse :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = false := by
    intro hfalse
    have hzero :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair false).mpr hfalse
    rw [hgroup] at hzero
    simp at hzero
  have hnottrue :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = true := by
    intro htrue
    have hone :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair true).mpr htrue
    rw [hgroup] at hone
    simp at hone
  have hexfalse :
      ∃ parent ∈ pair.val, parents parent coordinate = false := by
    by_contra hnone
    push Not at hnone
    apply hnottrue
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  have hextrue :
      ∃ parent ∈ pair.val, parents parent coordinate = true := by
    by_contra hnone
    push Not at hnone
    apply hnotfalse
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  obtain ⟨falseParent, hfalseParent, hfalseBit⟩ := hexfalse
  obtain ⟨trueParent, htrueParent, htrueBit⟩ := hextrue
  let mismatches : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
  let agreements : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        ¬ parents parent coordinate ≠ children pair coordinate)
  have hmismatch : mismatches.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨trueParent, ?_⟩
      simp [mismatches, htrueParent, htrueBit, hchild]
    · refine ⟨falseParent, ?_⟩
      simp [mismatches, hfalseParent, hfalseBit, hchild]
  have hagreement : agreements.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨falseParent, ?_⟩
      simp [agreements, hfalseParent, hfalseBit, hchild]
    · refine ⟨trueParent, ?_⟩
      simp [agreements, htrueParent, htrueBit, hchild]
  have hpartition : mismatches.card + agreements.card = 2 := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pair.val)
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
    change mismatches.card + agreements.card = pair.val.card at hfilter
    simpa [pair.property] using hfilter
  have hmismatch_pos := Finset.card_pos.mpr hmismatch
  have hagreement_pos := Finset.card_pos.mpr hagreement
  change mismatches.card = 1
  omega

theorem pairCoordinatePairMismatchCount_sum_false
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 0,
        if children pair coordinate = true then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 0)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair false hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
      rw [← Finset.sum_filter]
      simp [pairTypeGroupChildOnes, Nat.mul_comm]

theorem pairCoordinatePairMismatchCount_sum_true
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  let zeroChildren : Finset (PairLayer parentCount 1) :=
    (pairTypeGroup parents coordinate 1).filter
      (fun pair => children pair coordinate = false)
  have hpartition :
      (pairTypeGroupChildOnes parents children coordinate 1).card +
        zeroChildren.card =
          (pairTypeGroup parents coordinate 1).card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pairTypeGroup parents coordinate 1)
      (fun pair => children pair coordinate = true)
    simpa [pairTypeGroupChildOnes, zeroChildren] using hfilter
  have hzero_card :
      zeroChildren.card =
        (pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card := by
    omega
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 1,
        if children pair coordinate = false then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 1)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair true hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * zeroChildren.card := by
      rw [← Finset.sum_filter]
      simp [zeroChildren, Nat.mul_comm]
    _ = 2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
      rw [hzero_card]

theorem pairCoordinatePairMismatchCount_sum_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      (pairTypeGroup parents coordinate 2).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ _pair ∈ pairTypeGroup parents coordinate 2, 1 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 2)) := by
          simpa only [pairTypeGroup] using hpair
        exact pairCoordinatePairMismatchCount_mixed
          parents children coordinate pair
            (Finset.mem_filter.mp hmembership).2
    _ = (pairTypeGroup parents coordinate 2).card := by
      simp

theorem sum_pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair : PairLayer parentCount 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card +
      (pairTypeGroup parents coordinate 2).card +
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to hmaps
      (fun pair =>
        pairCoordinatePairMismatchCount
          parents children coordinate pair)).symm
  have hpartition :
      (∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
        (∑ pair ∈ pairTypeGroup parents coordinate 0,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 2,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) := by
    simpa [pairTypeGroup, Fin.sum_univ_succ, add_assoc] using hfiber
  rw [pairCoordinatePairMismatchCount_sum_false,
    pairCoordinatePairMismatchCount_sum_true,
    pairCoordinatePairMismatchCount_sum_mixed] at hpartition
  omega

theorem sum_pairCoordinatePairMismatchCount_eq_hammingDist
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
      ∑ pair : PairLayer parentCount 1,
        ∑ parent ∈ pair.val,
          hammingDist (parents parent) (children pair) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pair _
  have hcount (coordinate : Fin dimension) :
      pairCoordinatePairMismatchCount parents children coordinate pair =
        ∑ parent ∈ pair.val,
          if parents parent coordinate ≠ children pair coordinate
            then 1 else 0 := by
    change
      (pair.val.filter
        (fun parent =>
          parents parent coordinate ≠ children pair coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro parent _
  change
    (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children pair coordinate
        then 1 else 0) =
      ((Finset.univ : Finset (Fin dimension)).filter
        (fun coordinate =>
          parents parent coordinate ≠ children pair coordinate)).card
  exact Finset.sum_boole _ _

theorem pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair : ℕ) : ℝ) /
        (2 * (parentCount.choose 2 : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hone := pairTypeGroupChildOnes_card_le
    parents children coordinate 1
  rw [pairCoordinateKernel_empiricalAverageDisagreement
    hparents parents children coordinate,
    sum_pairCoordinatePairMismatchCount]
  push_cast [hone]
  field_simp [hpair.ne']

theorem pairChildArrayAverageDisagreement_le_radius
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges :
      ∀ (pair : PairLayer parentCount 1)
        (parent : PairLayer parentCount 0),
        parent ∈ pair.val →
          hammingDist (parents parent) (children pair) ≤ radius) :
    pairChildArrayAverageDisagreement hparents parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ parentCount)
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) ≤
        2 * parentCount.choose 2 * radius := by
    calc
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) =
        ∑ pair : PairLayer parentCount 1,
          ∑ parent ∈ pair.val,
            hammingDist (parents parent) (children pair) :=
        sum_pairCoordinatePairMismatchCount_eq_hammingDist
          parents children
      _ ≤ ∑ pair : PairLayer parentCount 1,
          ∑ _parent ∈ pair.val, radius := by
        apply Finset.sum_le_sum
        intro pair _
        apply Finset.sum_le_sum
        intro parent hparent
        exact hedges pair parent hparent
      _ = ∑ _pair : PairLayer parentCount 1, 2 * radius := by
        apply Finset.sum_congr rfl
        intro pair _
        simp [pair.property]
      _ = 2 * parentCount.choose 2 * radius := by
        simp [pairLayer_card_succ, pairLayer_card_zero,
          Nat.mul_assoc, Nat.mul_comm]
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair : ℕ) : ℝ)) ≤
        2 * (parentCount.choose 2 : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  unfold pairChildArrayAverageDisagreement
  simp_rw [pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    (by omega : 2 ≤ parentCount) parents children]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdimension_real).mpr
  apply (div_le_iff₀ (mul_pos (by norm_num) hpair)).mpr
  nlinarith

theorem pairGraphCopy_parent_child_hammingDist_le
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (pair :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (parent :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 0)
    (hparent : parent ∈ pair.val) :
    hammingDist
      (pairGraphCopyParentWords retained copy layer parent)
      (pairGraphCopyChildWords retained copy layer pair) ≤ radius := by
  have hactualParent :
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        ((pairLayerPairEquiv baseSize layer.val) pair).val := by
    change
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        pair.val.map
          (pairLayerFinEquiv baseSize layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := pairGraph_parent_child_adj
    baseSize depth layer.val (by omega)
      ((pairLayerPairEquiv baseSize layer.val) pair)
      ((pairLayerFinEquiv baseSize layer.val).symm parent)
      hactualParent
  have hedge := copy.toHom.map_rel hsource
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) pair))).val
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          ((pairLayerFinEquiv baseSize layer.val).symm parent))).val at hedge
  have hdist :=
    ((hammingHost_adj_iff dimension radius _ _).mp hedge).2
  simpa [pairGraphCopyParentWords, pairGraphCopyChildWords,
    hammingDist_comm] using hdist

theorem pairGraphCopy_averageDisagreement_le_radius
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) := by
  apply pairChildArrayAverageDisagreement_le_radius
    (hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase))
    hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
    radius
  intro pair parent hparent
  exact pairGraphCopy_parent_child_hammingDist_le
    retained copy layer pair parent hparent

theorem pairGraphCopy_averageDisagreement_le_tau
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤ tau := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) :=
      pairGraphCopy_averageDisagreement_le_radius
        hbase hdimension retained copy layer
    _ ≤ tau :=
      (div_le_iff₀ hdimension_real).mpr hradius

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  apply pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    hbase hdimension hdepth retained hexclusion herror
  intro copy layer
  exact pairGraphCopy_averageDisagreement_le_tau
    hbase hdimension hradius retained copy layer
