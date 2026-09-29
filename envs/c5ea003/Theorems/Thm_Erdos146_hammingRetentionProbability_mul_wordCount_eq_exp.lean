-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_eq_exp
-- name    : Erdos146.hammingRetentionProbability_mul_wordCount_eq_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:46:48.48855+00:00
-- url     : https://prove2.me/theorems/4333cf75-d185-42dc-ad85-624bc8eda7de
-- title:
--   Retention probability times word count, in exponential form
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The product of the retention probability and the number of words is $2^{(1-\beta)m}$, the exponential form used to compare with the extremal power.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14680-L14694

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionProbability_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - midpointBeta) * (dimension : ℝ) * Real.log 2) := by sorry
