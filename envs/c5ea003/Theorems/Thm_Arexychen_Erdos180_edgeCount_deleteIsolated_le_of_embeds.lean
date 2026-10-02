-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_deleteIsolated_le_of_embeds
-- name    : Arexychen.Erdos180.edgeCount_deleteIsolated_le_of_embeds
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:59.227677+00:00
-- url     : https://prove2.me/theorems/a130fa6c-3647-4324-aed2-77a98e181f90
-- title:
--   Ordinary containment bounds the reduced edge count
-- statement:
--   Let $H$ and $G$ be simple graphs on arbitrary vertex types, and assume the edge set of $G$ is finite. If $H$ admits an injective edge-preserving map into $G$, then the natural-number cardinality of the edge set of the graph obtained from $H$ by deleting isolated vertices is at most that of $G$. No finite-vertex assumption is required.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/OneEdge.lean#L12-L44

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180

theorem Arexychen.Erdos180.edgeCount_deleteIsolated_le_of_embeds
    {α : Type u} {β : Type v}
    (H : SimpleGraph α) (G : SimpleGraph β)
    [Finite G.edgeSet]
    (hemb : EmbedsAsSubgraph H G) :
    edgeCount (deleteIsolated H) ≤ edgeCount G := by sorry
