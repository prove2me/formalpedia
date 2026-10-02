-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_induce_compl_singleton
-- name    : Arexychen.Erdos180.edgeCount_induce_compl_singleton
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:26.800977+00:00
-- url     : https://prove2.me/theorems/a8337e10-bb1a-48c9-a92b-609741b3d218
-- title:
--   Counting edges after deleting one vertex
-- statement:
--   For a simple graph $G$ on a finite vertex type with decidable adjacency, and any vertex $v$, the induced graph on the complement of $\{v\}$ satisfies
--
--   $$e(G-v)+\deg_G(v)=e(G).$$
--
--   Here $e$ is the natural-number cardinality of the unordered edge set.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Forest.lean#L14-L30

import Definitions.Def_arexychen_erdos180_core
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
attribute [local instance] SimpleGraph.neighborSetFintype
universe u v
open Arexychen.Erdos180

theorem Arexychen.Erdos180.edgeCount_induce_compl_singleton
    {α : Type u} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (v : α) :
    edgeCount (G.induce ({v}ᶜ : Set α)) + G.degree v = edgeCount G := by sorry
