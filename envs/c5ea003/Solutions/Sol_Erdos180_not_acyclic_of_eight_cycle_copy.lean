-- Prove2me | solution 1 for Erdos180.not_acyclic_of_eight_cycle_copy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:38:13.278162+00:00
-- url     : https://prove2.me/submissions/871e1d81-86bd-4d60-99c4-e124ec9ccde4

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Erdos180
open Finset SimpleGraph

theorem solution
    {α : Type*} {graph : SimpleGraph α}
    (copy : SimpleGraph.Copy (SimpleGraph.cycleGraph 8) graph) :
    ¬ graph.IsAcyclic := by
  intro hacyclic
  have hcycle : (SimpleGraph.cycleGraph 8).IsAcyclic :=
    hacyclic.comap copy.toHom copy.injective
  exact hcycle (SimpleGraph.cycleGraph.cycle 5)
    (SimpleGraph.cycleGraph.isCycle_cycle)
