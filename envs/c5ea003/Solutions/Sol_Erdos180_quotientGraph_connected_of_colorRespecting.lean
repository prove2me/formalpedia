-- Prove2me | solution 1 for Erdos180.quotientGraph_connected_of_colorRespecting
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:26:12.60607+00:00
-- url     : https://prove2.me/submissions/1c7238bc-b6c5-49e9-b674-1c73ee548f4e

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Erdos180
open Finset SimpleGraph

theorem solution
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f)
    (hconnected : graph.Connected) :
    (quotientGraph graph f).Connected := by
  refine SimpleGraph.Connected.map
    (colorRespectingQuotientProjectionHom graph color hproper f hf)
    ?_ hconnected
  rintro ⟨_, ⟨v, rfl⟩⟩
  exact ⟨v, rfl⟩
