-- Prove2me | Theorems.Thm_Erdos146_hammingWordNeighbor_sum_const
-- name    : Erdos146.hammingWordNeighbor_sum_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:50:21.608276+00:00
-- url     : https://prove2.me/theorems/5d4f7c62-91e2-4b3e-a314-aadbd2add26c
-- title:
--   Neighbour counts are constant over words
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. Every word has the same number of neighbours in the host, by vertex-transitivity of the Hamming metric.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L15990-L16008

import Definitions.Def_erdos146_core2
import Mathlib.InformationTheory.Hamming

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingWordNeighbor_sum_const
    (dimension radius : ℕ) (left : HammingWord dimension)
    (weight : ℝ) :
    (∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then weight else 0) =
      ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) * weight := by sorry
