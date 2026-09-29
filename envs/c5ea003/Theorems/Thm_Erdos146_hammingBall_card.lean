-- Prove2me | Theorems.Thm_Erdos146_hammingBall_card
-- name    : Erdos146.hammingBall_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:49:55.32242+00:00
-- url     : https://prove2.me/theorems/2c340e38-aaf9-4a44-80ec-d468e8f0d0d6
-- title:
--   Cardinality of a Hamming ball
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The number of words within Hamming distance $k$ of a given word is the corresponding partial sum of binomial coefficients — the host's degree.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L15937-L15950

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingBall_card (dimension radius : ℕ)
    (u : HammingWord dimension) :
    (hammingBall dimension radius u).card =
      ∑ d ∈ Finset.range (radius + 1), dimension.choose d := by sorry
