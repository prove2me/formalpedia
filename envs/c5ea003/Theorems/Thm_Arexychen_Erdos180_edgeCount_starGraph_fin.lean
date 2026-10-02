-- Prove2me | Theorems.Thm_Arexychen_Erdos180_edgeCount_starGraph_fin
-- name    : Arexychen.Erdos180.edgeCount_starGraph_fin
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:12.251195+00:00
-- url     : https://prove2.me/theorems/1694045f-d155-42b4-a0ae-302db83dbf43
-- title:
--   A star on $n$ labelled vertices has $n-1$ edges
-- statement:
--   For a natural number $n\ge1$, the star on $\operatorname{Fin}(n)$ with center $0$ has exactly $n-1$ unordered edges. The case $n=1$ is included and has no edges.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Star.lean#L12-L43

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

theorem Arexychen.Erdos180.edgeCount_starGraph_fin {n : ℕ} (hn : 1 ≤ n) :
    edgeCount (starGraph (⟨0, by omega⟩ : Fin n)) = n - 1 := by sorry
