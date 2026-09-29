-- Prove2me | solution 1 for Erdos146.binomialProbabilityMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:06:10.540421+00:00
-- url     : https://prove2.me/submissions/c9c45a1c-7b3a-4cab-bb35-01ef8212cd39

import Definitions.Def_erdos146_core2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Ring.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (trialCount successCount : ℕ) (probability : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity
