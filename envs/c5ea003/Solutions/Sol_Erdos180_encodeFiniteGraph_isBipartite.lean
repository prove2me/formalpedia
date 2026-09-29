-- Prove2me | solution 1 for Erdos180.encodeFiniteGraph_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:28:17.106382+00:00
-- url     : https://prove2.me/submissions/16b6e671-c02a-46c6-8d1c-30710142e14d

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem solution
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hbipartite : graph.IsBipartite) :
    (encodeFiniteGraph graph).graph.IsBipartite := by
  classical
  exact SimpleGraph.Colorable.map
    (Fintype.equivFin V).toEmbedding hbipartite
