-- Prove2me | Theorems.Thm_Erdos146_hammingExpectedRetainedEdgeCount_eq
-- name    : Erdos146.hammingExpectedRetainedEdgeCount_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:50:59.113586+00:00
-- url     : https://prove2.me/theorems/af3fe13e-224c-4d94-99cc-c06a5e13fef7
-- title:
--   Expected number of retained edges
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The expected number of retained edges is $p^2$ times the number of host edges. Comparing this with the expected vertex count to the power $3/2$ is exactly what the threshold $C(\tau) = 2h(\tau) - 1$ measures.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L16212-L16231

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingExpectedRetainedEdgeCount_eq
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeCount dimension radius =
      hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) := by sorry
