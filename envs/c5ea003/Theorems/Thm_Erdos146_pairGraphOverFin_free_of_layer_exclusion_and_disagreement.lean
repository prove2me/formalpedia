-- Prove2me | Theorems.Thm_Erdos146_pairGraphOverFin_free_of_layer_exclusion_and_disagreement
-- name    : Erdos146.pairGraphOverFin_free_of_layer_exclusion_and_disagreement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:52:15.363448+00:00
-- url     : https://prove2.me/theorems/bb4470d2-fe56-4888-a974-6ba017f88e04
-- title:
--   Layer exclusion plus disagreement, on the finite model
-- statement:
--   Step in the exclusion argument of Sections 7 and 8. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. Lemma 7.1 excludes, with probability at least $1 - 2s\,2^{-m}$, any parent array of length $L_{i-1}$ together with a pairwise distinct retained child array of length $L_i$ satisfying $E(u,z) \le \beta - \delta$. The same conclusion transported to the finite index model of the layered graph.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17532-L17563

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    {baseSize depth dimension radius : ℕ}
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
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by sorry
