-- Prove2me | solution 1 for Erdos146.pairGraphCopy_layer_entropy_upper_of_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:41:04.040488+00:00
-- url     : https://prove2.me/submissions/140e803c-5158-4aaa-bf2e-eb09fee648d3

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Theorems.Thm_Erdos146_booleanWordOnes_card_equiv
import Theorems.Thm_Erdos146_pairChildArrayEntropy_empirical_bound

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairGraphCopy_parentPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairParentArrayEntropyPotential
        (pairGraphCopyParentWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val, by omega⟩ := by
  unfold pairParentArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount pairGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (pairLayerFinEquiv baseSize layer.val).symm
    (fun vertex : PairLayer baseSize layer.val =>
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          vertex)).val.2 coordinate)]

theorem pairGraphCopy_childPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayEntropyPotential
        (pairGraphCopyChildWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val + 1, by omega⟩ := by
  unfold pairChildArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairChildCoordinateOneCount pairGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (pairLayerPairEquiv baseSize layer.val)
    (fun vertex : PairLayer baseSize (layer.val + 1) =>
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          vertex)).val.2 coordinate)]
  rw [pairLayer_card_succ]

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdisagreement :
      pairChildArrayAverageDisagreement
        (hbase.trans
          (pairLayer_card_ge_base baseSize layer.val hbase))
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    pairChildArrayEntropy
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        entropyLowerEndpoint +
          (pairGraphCopyLayerPotential retained copy
              ⟨layer.val + 1, by omega⟩ -
            pairGraphCopyLayerPotential retained copy
              ⟨layer.val, by omega⟩) / 2 +
          empiricalEntropyError
            (Fintype.card (PairLayer baseSize layer.val)) := by
  have hparents :
      4 ≤ Fintype.card (PairLayer baseSize layer.val) :=
    hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase)
  have hbound := pairChildArrayEntropy_empirical_bound
    hparents hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
  rw [pairGraphCopy_childPotential_eq retained copy layer,
    pairGraphCopy_parentPotential_eq retained copy layer] at hbound
  have hscaled := mul_le_mul_of_nonneg_left
    hdisagreement logTwo_three_pos.le
  unfold entropyLowerEndpoint
  nlinarith
