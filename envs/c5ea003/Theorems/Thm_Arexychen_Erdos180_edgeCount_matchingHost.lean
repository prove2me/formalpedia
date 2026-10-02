-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_matchingHost
-- name    : Arexychen.Erdos180.edgeCount_matchingHost
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:26.831172+00:00
-- url     : https://prove2.me/theorems/1c127416-6f57-4c65-8599-99237d3977f9
-- title:
--   The labelled matching host has $\lfloor n/2\rfloor$ edges
-- statement:
--   For every natural number $n$, the graph on $\operatorname{Fin}(n)$ consisting of the disjoint pairs $\{0,1\},\{2,3\},\ldots$ has exactly $\lfloor n/2\rfloor$ unordered edges. An odd last vertex is isolated; the assertion also includes $n=0$ and $n=1$.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Matching.lean#L86-L129

import Definitions.Def_arexychen_erdos180_core
import Definitions.Def_arexychen_erdos180_families_matching
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

theorem Arexychen.Erdos180.edgeCount_matchingHost (n : ℕ) :
    edgeCount (matchingHost n) = n / 2 := by sorry
