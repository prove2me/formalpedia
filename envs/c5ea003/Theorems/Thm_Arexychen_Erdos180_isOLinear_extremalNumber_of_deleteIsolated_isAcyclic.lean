-- Prove2me | Theorems.Thm_Arexychen_Erdos180_isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
-- name    : Arexychen.Erdos180.isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:19:50.961722+00:00
-- url     : https://prove2.me/theorems/7b491711-e3cd-49a4-a0be-4b0294d1f82e
-- title:
--   The extremal function of a reduced forest is $O(n)$
-- statement:
--   For a finite simple graph $H$ whose induced graph on non-isolated vertices is acyclic, the function $n\mapsto\operatorname{ex}_H(n)$ is $O(n)$ as natural $n$ tends to infinity. The extremal value is the natural-number supremum of edge counts of $H$-free graphs on $\operatorname{Fin}(n)$, using ordinary subgraph containment of the whole $H$. The asymptotic comparison casts these values and $n$ to real numbers.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Forest.lean#L379-L394

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

theorem Arexychen.Erdos180.isOLinear_extremalNumber_of_deleteIsolated_isAcyclic
    {α : Type u} [Fintype α] (H : SimpleGraph α)
    (hforest : (deleteIsolated H).IsAcyclic) :
    IsOLinear (fun n => extremalNumber H n) := by sorry
