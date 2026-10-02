-- Prove2me | Theorems.Thm_Arexychen_Erdos180_matchingHost_isMatchingGraph
-- name    : Arexychen.Erdos180.matchingHost_isMatchingGraph
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:01.176464+00:00
-- url     : https://prove2.me/theorems/0b10d205-b00f-41f5-95cf-ca5df5caa1dc
-- title:
--   The labelled matching host has at most one neighbor per vertex
-- statement:
--   For every natural number $n$, each vertex of the labelled graph with pairs $\{0,1\},\{2,3\},\ldots$ has at most one neighbor: if it is adjacent to both $y$ and $z$, then $y=z$. Isolated vertices are permitted.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Matching.lean#L44-L80

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

theorem Arexychen.Erdos180.matchingHost_isMatchingGraph (n : ℕ) :
    IsMatchingGraph (matchingHost n) := by sorry
