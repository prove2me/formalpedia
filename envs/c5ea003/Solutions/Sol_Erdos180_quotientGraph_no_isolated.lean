-- Prove2me | solution 1 for Erdos180.quotientGraph_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:49:47.940019+00:00
-- url     : https://prove2.me/submissions/b8009164-6f73-4226-a933-4d653f1e9544

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph

theorem solution
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v)
    (f : V → V) (hf : ColorRespecting color f) :
    ∀ u : Set.range f,
      ∃ v : Set.range f, (quotientGraph graph f).Adj u v := by
  rintro ⟨_, ⟨u, rfl⟩⟩
  obtain ⟨v, huv⟩ := hneighbors u
  refine ⟨⟨f v, v, rfl⟩, ?_⟩
  exact (colorRespectingQuotientProjectionHom
    graph color hproper f hf).map_rel huv
