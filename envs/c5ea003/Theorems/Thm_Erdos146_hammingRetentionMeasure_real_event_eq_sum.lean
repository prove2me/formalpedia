-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_real_event_eq_sum
-- name    : Erdos146.hammingRetentionMeasure_real_event_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:48:15.23005+00:00
-- url     : https://prove2.me/theorems/dbbc90a2-b4e4-447d-adc8-eac0fdc49818
-- title:
--   Probability of a retention event as a sum
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The probability of a retention event is the sum of the retention weights of the configurations realising it.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14839-L14869

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.Real

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

open Classical in
theorem Erdos146.hammingRetentionMeasure_real_event_eq_sum
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (hammingRetentionMeasure dimension).real event =
      ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by sorry
