-- Prove2me | Theorems.Thm_Erdos146_pairGraphCopy_layer_entropy_upper_of_disagreement
-- name    : Erdos146.pairGraphCopy_layer_entropy_upper_of_disagreement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:51:50.046123+00:00
-- url     : https://prove2.me/theorems/f0ad1ef3-4d84-4ce6-a64e-dad7e0db55eb
-- title:
--   A copy of the layered graph forces low entropy at some layer
-- statement:
--   Step in the exclusion argument of Sections 7 and 8. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. Lemma 7.1 excludes, with probability at least $1 - 2s\,2^{-m}$, any parent array of length $L_{i-1}$ together with a pairwise distinct retained child array of length $L_i$ satisfying $E(u,z) \le \beta - \delta$. If a copy of the layered graph sits inside the retained host and its child words disagree as required, then at some layer the entropy potential is at most $\beta - \delta$ — that is, the copy exhibits exactly the low-entropy array Lemma 7.1 forbids.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17178-L17216

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphCopy_layer_entropy_upper_of_disagreement
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
            (Fintype.card (PairLayer baseSize layer.val)) := by sorry
