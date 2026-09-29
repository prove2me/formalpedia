-- Prove2me | solution 1 for Erdos180.encodeFiniteGraph_not_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:38:54.690099+00:00
-- url     : https://prove2.me/submissions/61c332f2-206e-4e5c-a255-1850e7ef3790

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Erdos180
open Finset SimpleGraph

theorem solution
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by
  intro hencoded
  apply h
  exact (SimpleGraph.Iso.map (Fintype.equivFin α) graph).isAcyclic_iff.mpr
    hencoded
