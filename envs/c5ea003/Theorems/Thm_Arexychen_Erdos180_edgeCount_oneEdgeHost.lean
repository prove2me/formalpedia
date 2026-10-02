-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_oneEdgeHost
-- name    : Arexychen.Erdos180.edgeCount_oneEdgeHost
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:10.559632+00:00
-- url     : https://prove2.me/theorems/b74caad5-daf6-4b7f-81f7-43f392c2346f
-- title:
--   The labelled one-edge host has exactly one edge
-- statement:
--   For every natural number $n\ge2$, the graph on $\operatorname{Fin}(n)$ with the sole unordered edge $\{0,1\}$ has edge count one. All other vertices are isolated.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/OneEdge.lean#L67-L88

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_oneedge
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

theorem Arexychen.Erdos180.edgeCount_oneEdgeHost {n : ℕ} (hn : 2 ≤ n) :
    edgeCount (oneEdgeHost n hn) = 1 := by sorry
