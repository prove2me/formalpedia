-- Prove2me | solution 1 for LeblRA.countable_dense_subset_11_6_8
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:37.733818+00:00
-- url     : https://prove2.me/submissions/cd1a7f84-f156-4ad1-88a9-e3e1320b23c9

import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
open Filter Set Topology
open scoped UniformConvergence
universe u

theorem solution {X : Type u} [MetricSpace X] [CompactSpace X] :
    ∃ D : Set X, D.Countable ∧ Dense D := by
  exact TopologicalSpace.exists_countable_dense X
