-- Prove2me | solution 1 for Erdos146.pairGraphOverFin_free_of_manuscript_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:47:37.123784+00:00
-- url     : https://prove2.me/submissions/7e7e3fd0-aa5a-4082-9716-2ca8df0ef7f7

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic
import Theorems.Thm_Erdos146_manuscriptHammingRadius_le
import Theorems.Thm_Erdos146_pairGraphOverFin_free_of_layer_exclusion

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {baseSize depth dimension : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
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
      (retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained) := by
  exact pairGraphOverFin_free_of_layer_exclusion
    hbase hdimension hdepth
    (manuscriptHammingRadius_le dimension)
    retained hexclusion herror
