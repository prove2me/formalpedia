-- Prove2me | Theorems.Thm_Erdos146_CompactnessConjecture_free_map_of_no_isolated
-- name    : Erdos146.CompactnessConjecture.free_map_of_no_isolated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:38:51.877753+00:00
-- url     : https://prove2.me/theorems/1a2a77ed-d32f-4368-85c4-f2933c0eda1a
-- title:
--   A homomorphism into a graph with no isolated vertices
-- statement:
--   A general graph-homomorphism fact shared with the compactness half of Chapter 10: if the source graph has no isolated vertices, a map witnessing freeness can be built as stated. It is reused here because the layered graph of Section 6 has no isolated vertices (Fact 6.1).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2649-L2682

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos146
open SimpleGraph

theorem Erdos146.CompactnessConjecture.free_map_of_no_isolated
    {U V W : Type*}
    (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    {host : SimpleGraph V}
    (embedding : V ↪ W)
    (hfree : forbidden.Free host) :
    forbidden.Free (host.map embedding) := by sorry
