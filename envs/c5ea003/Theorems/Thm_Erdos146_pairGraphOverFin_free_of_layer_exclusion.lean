-- Prove2me | Theorems.Thm_Erdos146_pairGraphOverFin_free_of_layer_exclusion
-- name    : Erdos146.pairGraphOverFin_free_of_layer_exclusion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:52:27.806177+00:00
-- url     : https://prove2.me/theorems/d13b89a5-6f88-4e9a-acb8-05b4f209b272
-- title:
--   Layer exclusion alone makes the host $H$-free
-- statement:
--   Step in the exclusion argument of Sections 7 and 8. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. Lemma 7.1 excludes, with probability at least $1 - 2s\,2^{-m}$, any parent array of length $L_{i-1}$ together with a pairwise distinct retained child array of length $L_i$ satisfying $E(u,z) \le \beta - \delta$. With the disagreement condition discharged, the exclusion of low-entropy arrays by itself makes the retained host free of the layered graph — Proposition 8.1's combinatorial content.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17565-L17588

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphOverFin_free_of_layer_exclusion
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
      (retainedHammingHost dimension radius retained) := by sorry
